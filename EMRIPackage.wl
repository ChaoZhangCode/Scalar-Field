(* ::Package:: *)

BeginPackage["MyPackage`"];


ZE::usage="ZE[l,m,k,p,e] for tensor field"
ZEscalar::usage="ZEscalar[l,m,k,p,e] for scalar field"
Psi::usage="Psi"
ELScalarFlux::usage="scalar"


Begin["`Private`"]
<<SpinWeightedSpheroidalHarmonics`


f=1-2/r;
RW[U_]:=f^2 D[\[Psi][r],{r,2}]+f D[f,r] D[\[Psi][r],r]+(\[Omega]^2-U)\[Psi][r]
Uodd[r_]:=f/r^2 (l(l+1)+(2M(1-s^2))/r);
rs[r_]:=r+2 Log[r/2-1];


ReggeWheelerInBC[s1_Integer, l1_Integer, \[Omega]1_, workingprecision_]:=
	Block[{s=s1,l=l1,i,A,a,n,\[Omega]=\[Omega]1,res,M=1,fH,err,r,rin=2+10^-5},
A[n_]:=((-1+2 n-n^2+s^2) a[-2+n]+(1+l+l^2-2 n+2 n^2-s^2) a[-1+n])/(n (n-4 I M \[Omega]));
a[-2]=0;
a[-1]=0;
a[0]=1;
fH=1-(2M)/r;
err=1;
res = Exp[-I \[Omega] rs[r]];
i=1;
While[err > 10^-workingprecision,
a[i]=A[i];
res+=Exp[-I \[Omega] rs[r]]a[i]fH^i;
err=Abs[RW[Uodd[r]]]/.{\[Psi][r]->res,Derivative[a_][\[Psi]][r]:>D[res,{r,a}]}/.r->rin;
i++;
];
{res,D[res,r],rin}/.r->rin
]


ReggeWheelerUpBC[s1_Integer,l1_Integer,\[Omega]1_,workingprecision_]:= Block[{s=s1,l=l1,A,a,n,\[Omega]=\[Omega]1,res,M=1,err,r,dres,d2res,rout, rsout,i},
rout =100\[Omega]^-1;
A[n_]:=(I (2 M \[Omega](1-2 n+n^2-s^2) a[-2+n]+(l+l^2+n-n^2) a[-1+n]))/(2 n );
a[-2]=0;
a[-1]=0;
a[0]=1;
err=1;
rsout = rs[rout];
res = Exp[I \[Omega] rsout];
dres = -((I E^(I \[Omega] rsout) rout \[Omega])/(2 M-rout));
d2res=-((E^(I \[Omega] rsout) \[Omega] (2 I M+rout^2 \[Omega]))/(-2 M+rout)^2);
i=1;
While[err > 10^-workingprecision,
a[i]=A[i];
res+=Exp[I \[Omega] rsout] a[i]/( \[Omega] rout)^i;
dres+=(E^(I \[Omega] rsout) (rout \[Omega])^-i (2 i M-i rout+I rout^2 \[Omega]) a[i])/(rout (-2 M+rout));
d2res+= (E^(I \[Omega] rsout) (rout \[Omega])^-i (i^2 (-2 M+rout)^2-rout^2 \[Omega] (2 I M+rout^2 \[Omega])+i (2 M-rout) (2 M+rout (-1+2 I rout \[Omega]))) a[i])/(rout^2 (-2 M+rout)^2);
err=Abs[RW[Uodd[r]]]/.{\[Psi][r]->res,\[Psi]'[r]->dres,\[Psi]''[r]->d2res}/.r->rout;
i++;
(*The infinity BCs is an asymptotic series so it might not converge.*)
If[i > 100, Break[]];
];
{res,dres,rout}
]


ReggeWheelerPotential[s_Integer,l_Integer,x_]:=(1-2/x)(2(1-s^2)+l(l+1)x)/x^3;


Integrator[s_,l_,\[Omega]_,y1BC_,y2BC_,xBC_,xmin_?NumericQ,xmax_?NumericQ,potential_,ndsolveopts___]:=Module[{y1,y2,x},
	Quiet[NDSolveValue[
		{y1'[x]==y2[x],(1-2/x)^2*y2'[x]+2(1-2/x)/x^2*y2[x]+(\[Omega]^2-potential[s,l,x])*y1[x]==0,y1[xBC]==y1BC,y2[xBC]==y2BC},
		y1,
		{x, xmin, xmax},
		ndsolveopts,
		Method->"StiffnessSwitching",
		MaxSteps->Infinity,
		InterpolationOrder->All
		], NDSolveValue::precw]
	]


Psi[s_, l_, \[Omega]_, bc_, pot_, ndsolveopts___][{xmin_, xmax_}] :=
 Module[{bcFunc, psiBC, dpsidxBC, xBC, xMin, xMax, soln, Potential},
    Potential = Switch[pot,"ReggeWheeler",ReggeWheelerPotential];
    bcFunc = Switch[pot,
        "ReggeWheeler", Lookup[<|"In" -> ReggeWheelerInBC, "Up" -> ReggeWheelerUpBC|>, bc]];
    {psiBC, dpsidxBC, xBC} = bcFunc[s, l, \[Omega], Lookup[{ndsolveopts}, WorkingPrecision, Precision[\[Omega]]]];
    If[bc === "In" && xmin === Automatic, xMin = xBC, xMin = xmin];
    If[bc === "Up" && xmax === Automatic, xMax = xBC, xMax = xmax];
    soln =Integrator[s, l, \[Omega], psiBC, dpsidxBC, xBC, xMin, xMax, Potential, ndsolveopts]
];


wronskian[r0_,psiin_,psiup_]:=Module[ {PsiIn,dPsiIn,PsiUp,dPsiUp,Wronskian,f},
f=1-2/r0;
PsiIn=psiin[r0];
dPsiIn=psiin'[r0];
PsiUp=psiup[r0];
dPsiUp=psiup'[r0];
Wronskian = f*PsiIn*dPsiUp - f*PsiUp*dPsiIn
]


ZE[l_,m_,k_,p_,e_]:=Module[{alllist,s,intfunction,RH0,RH1,RH2,chi1,t,f,r,\[Phi],p0,p1,p2,\[Omega],Qin,psiup,psiin,RH,M=1,chi,Gplus0,Gplus1,Gplus2,Gminus0,Gminus1,Gminus2,Zlmkout,Zlmkin},
s=-2;
r[\[Chi]_]:=p/(1+e Cos[\[Chi]]);
t[\[Chi]_]:=p^2 (p-2-2e)^(1/2) (p-2+2e)^(1/2) (1/((-1+e^2) (-4+p)^2 p^2 Sqrt[-6+p-2 e Cos[\[Chi]]]) (-2 (-1+e) (-4+p) p Sqrt[(-6+p-2 e Cos[\[Chi]])/(-6-2 e+p)] EllipticF[\[Chi]/2,(4 e)/(6+2 e-p)]-(4-p) p Sqrt[(-6+p-2 e Cos[\[Chi]])/(-6-2 e+p)] ((6+2 e-p) EllipticE[\[Chi]/2,(4 e)/(6+2 e-p)]+(-6+2 e+p) EllipticF[\[Chi]/2,(4 e)/(6+2 e-p)])-(2 (-4+p) (-8+e^2 (8-3 p)-p+p^2) Sqrt[(-6+p-2 e Cos[\[Chi]])/(-6-2 e+p)] EllipticPi[(2 e)/(1+e),\[Chi]/2,(4 e)/(6+2 e-p)])/(1+e)+(8 (-1+e^2) (-4+p)^2 Sqrt[(-6+p-2 e Cos[\[Chi]])/(-6-2 e+p)] EllipticPi[(4 e)/(2+2 e-p),\[Chi]/2,(4 e)/(6+2 e-p)])/(-2-2 e+p)+(e (-4+p) p (-6+p-2 e Cos[\[Chi]]) Sin[\[Chi]])/(1+e Cos[\[Chi]])));
\[Phi][\[Chi]_]:=p^(1/2) (2  EllipticF[\[Chi]/2,-((4 e)/(-6-2 e+p))])/Sqrt[-6-2 e+p];
\[Omega]=m*Re[(2\[Phi][Pi])/(2t[Pi])]+k*Re[(2Pi)/(2t[Pi])];
If[\[Omega]>0,
psiup=Psi[s,l,SetPrecision[\[Omega],$MachinePrecision],"Up","ReggeWheeler",PrecisionGoal->10,AccuracyGoal->Infinity][{2+10^-5,1500}];
psiin=Psi[s,l,SetPrecision[\[Omega],$MachinePrecision],"In","ReggeWheeler",PrecisionGoal->10,AccuracyGoal->Infinity][{2+10^-5,1500}];
f[chi_]:=1-2M/r[chi];
RH0[chi_]:=RH[p/(1+e Cos[chi])];
RH1[chi1_]:=-r[chi1] f[chi1] RH'[p/(1+e Cos[chi1])]+(2f[chi1]+I \[Omega] r[chi1])RH[p/(1+e Cos[chi1])];
RH2[chi_]:=r[chi]^2 f[chi]^2 RH''[p/(1+e Cos[chi])]-2r[chi] f[chi](f[chi]+I \[Omega] r[chi])RH'[p/(1+e Cos[chi])]+I \[Omega] r[chi](2-2 M/r[chi]+I \[Omega] r[chi])RH[p/(1+e Cos[chi])];
Qin=-1/(4 \[Omega]^2) ((l-1)l(l+1)(l+2)-12I M \[Omega]) wronskian[100,psiin,psiup]/(2I);
Gplus0[chi_]:=1/(4r[chi]^4 (1-2 M/r[chi])^2) r[chi]^2 (Sqrt[((p-2-2e)(p-2+2e))/(p(p-3-e^2))]+e Sin[chi]((p-6-2e Cos[chi])/(p(p-3-e^2)))^(1/2))^2;
Gminus0[chi_]:=1/(4r[chi]^4 (1-2 M/r[chi])^2) r[chi]^2 (Sqrt[((p-2-2e)(p-2+2e))/(p(p-3-e^2))]-e Sin[chi]((p-6-2e Cos[chi])/(p(p-3-e^2)))^(1/2))^2;
Gplus1[chi_]:=1/(4r[chi]^4 (1-2 M/r[chi])^2) Sqrt[2]I r[chi]Sqrt[p^2/(p-3-e^2)](Sqrt[((p-2-2e)(p-2+2e))/(p(p-3-e^2))]+e Sin[chi]((p-6-2e Cos[chi])/(p(p-3-e^2)))^(1/2));
Gminus1[chi_]:=1/(4r[chi]^4 (1-2 M/r[chi])^2) Sqrt[2]I r[chi] Sqrt[p^2/(p-3-e^2)](Sqrt[((p-2-2e)(p-2+2e))/(p(p-3-e^2))]-e Sin[chi]((p-6-2e Cos[chi])/(p(p-3-e^2)))^(1/2));
Gplus2[chi_]:=1/(4r[chi]^4 (1-2 M/r[chi])^2) (-2 (Sqrt[p^2/(p-3-e^2)])^2);
Gminus2[chi_]:=1/(4r[chi]^4 (1-2 M/r[chi])^2) (-2 (Sqrt[p^2/(p-3-e^2)])^2);
p0[chi_]:=2((l-1)l(l+1)(l+2))^(1/2) SpinWeightedSphericalHarmonicY[0, l, m,Pi/2, 0] (2Pi)/(2t[Pi]) ( p /(1+e Cos[chi])^2 RH0[chi])/ (((p-6-2e Cos[chi])/(p(p-3-e^2)))^(1/2)) (Gplus0[chi]*Exp[+I (\[Omega] t[chi]-m \[Phi][chi])]+Gminus0[chi]*Exp[-I (\[Omega] t[chi]-m \[Phi][chi])]);

p1[chi_]:=2^(3/2) ((l-1)(l+2))^(1/2) SpinWeightedSphericalHarmonicY[-1, l, m,Pi/2, 0] (2Pi)/(2t[Pi]) ( p /(1+e Cos[chi])^2 RH1[chi])/ (((p-6-2e Cos[chi])/(p(p-3-e^2)))^(1/2)) (Gplus1[chi]*Exp[+I (\[Omega] t[chi]-m \[Phi][chi])]+Gminus1[chi]*Exp[-I (\[Omega] t[chi]-m \[Phi][chi])]);
p2[chi_]:=SpinWeightedSphericalHarmonicY[-2, l, m,Pi/2, 0] (2Pi)/(2t[Pi]) ( p /(1+e Cos[chi])^2 RH2[chi])/ (((p-6-2e Cos[chi])/(p(p-3-e^2)))^(1/2)) (Gplus2[chi]*Exp[+I (\[Omega] t[chi]-m \[Phi][chi])]+Gminus2[chi]*Exp[-I (\[Omega] t[chi]-m \[Phi][chi])]);
intfunction[chi_]:=p0[chi]+p1[chi]+p2[chi];
RH[r0_]:=((12 M^2-2 M r0 (3+l+l^2+3 I r0 \[Omega])+r0^2 (l+l^2-2 r0 \[Omega] (-I+r0 \[Omega]))) psiin[r0])/r0+2 (2 M-r0) (3 M+r0 (-1-I r0 \[Omega])) Derivative[1][psiin][r0];
Zlmkout=(2I \[Omega]^2 Qin)^-1 Quiet[NIntegrate[intfunction[chi10],{chi10,0,\[Pi]}]];
RH[r0_]:=((12 M^2-2 M r0 (3+l+l^2+3 I r0 \[Omega])+r0^2 (l+l^2-2 r0 \[Omega] (-I+r0 \[Omega]))) psiup[r0])/r0+2 (2 M-r0) (3 M+r0 (-1-I r0 \[Omega])) Derivative[1][psiup][r0];
If[l<=4 && l==m,Zlmkin=(2I \[Omega]^2 Qin)^-1 Quiet[NIntegrate[intfunction[chi10],{chi10,0,\[Pi]}]],Zlmkin=0];
alllist={1/(4Pi) \[Omega]^2 Abs[Zlmkout]^2,1/(4Pi) \[Omega] m*Abs[Zlmkout]^2,1/(4Pi) \[Omega]^2 Abs[Zlmkin]^2,1/(4Pi) \[Omega] m*Abs[Zlmkin]^2};
If[m==0,2alllist,2alllist]
,{0,0,0,0}]
]


ZEscalar[l_,m_,k_,p_,e_]:=Module[{alllist,s,intfunction,RH0,RH1,RH2,chi1,t,f,r,\[Phi],p0,p1,p2,\[Omega],Ain,psiup,psiin,RH,M=1,chi,Gplus0,Gplus1,Gplus2,Gminus0,Gminus1,Gminus2,Zlmkout,Zlmkin},
s=0;
f[chi_]:=1-2M/r[chi];
r[\[Chi]_]:=p/(1+e Cos[\[Chi]]);
t[\[Chi]_]:=p^2 (p-2-2e)^(1/2) (p-2+2e)^(1/2) (1/((-1+e^2) (-4+p)^2 p^2 Sqrt[-6+p-2 e Cos[\[Chi]]]) (-2 (-1+e) (-4+p) p Sqrt[(-6+p-2 e Cos[\[Chi]])/(-6-2 e+p)] EllipticF[\[Chi]/2,(4 e)/(6+2 e-p)]-(4-p) p Sqrt[(-6+p-2 e Cos[\[Chi]])/(-6-2 e+p)] ((6+2 e-p) EllipticE[\[Chi]/2,(4 e)/(6+2 e-p)]+(-6+2 e+p) EllipticF[\[Chi]/2,(4 e)/(6+2 e-p)])-(2 (-4+p) (-8+e^2 (8-3 p)-p+p^2) Sqrt[(-6+p-2 e Cos[\[Chi]])/(-6-2 e+p)] EllipticPi[(2 e)/(1+e),\[Chi]/2,(4 e)/(6+2 e-p)])/(1+e)+(8 (-1+e^2) (-4+p)^2 Sqrt[(-6+p-2 e Cos[\[Chi]])/(-6-2 e+p)] EllipticPi[(4 e)/(2+2 e-p),\[Chi]/2,(4 e)/(6+2 e-p)])/(-2-2 e+p)+(e (-4+p) p (-6+p-2 e Cos[\[Chi]]) Sin[\[Chi]])/(1+e Cos[\[Chi]])));
\[Phi][\[Chi]_]:=p^(1/2) (2  EllipticF[\[Chi]/2,-((4 e)/(-6-2 e+p))])/Sqrt[-6-2 e+p];
\[Omega]=m*Re[(2\[Phi][Pi])/(2t[Pi])]+k*Re[(2Pi)/(2t[Pi])];
If[\[Omega]>0 && Element[\[Omega],Reals] ,
psiup=Psi[s,l,SetPrecision[\[Omega],$MachinePrecision],"Up","ReggeWheeler",PrecisionGoal->10,AccuracyGoal->Infinity][{2+10^-5,1500}];
psiin=Psi[s,l,SetPrecision[\[Omega],$MachinePrecision],"In","ReggeWheeler",PrecisionGoal->10,AccuracyGoal->Infinity][{2+10^-5,1500}];
RH0[chi_]:=RH[p/(1+e Cos[chi])] 1/r[chi] ;
Ain= wronskian[100,psiin,psiup]/(2I \[Omega]);
p0[chi_]:=1/(2Pi) SpinWeightedSphericalHarmonicY[0, l, m,Pi/2, 0] (2Pi)/(2t[Pi]) (p /(1+e Cos[chi])^2 RH0[chi])/(((p-6-2e Cos[chi])/(p(p-3-e^2)))^(1/2)) (Exp[+I (\[Omega] t[chi]-m \[Phi][chi])]+Exp[-I (\[Omega] t[chi]-m \[Phi][chi])]);
intfunction[chi_]:=p0[chi];

RH[r0_]:= psiin[r0];
Zlmkout=(2I \[Omega] Ain)^-1 Quiet[NIntegrate[intfunction[chi10],{chi10,0,\[Pi]}]];
RH[r0_]:= psiup[r0];
If[l<=4 && l==m,Zlmkin=(2I \[Omega] Ain)^-1 Quiet[NIntegrate[intfunction[chi10],{chi10,0,\[Pi]}]],Zlmkin=0];
alllist={\[Omega]^2 Abs[Zlmkout]^2,\[Omega] m Abs[Zlmkout]^2, \[Omega]^2 Abs[Zlmkin]^2,\[Omega] m Abs[Zlmkin]^2};
If[m==0,2alllist,2alllist],{0,0,0,0}]
]


ELFlux[p_,e_,lmax_,kmin_,kmax_]:=Module[{energyangularlist,energyout,angularout,energyin,angularin},
energyangularlist=ParallelTable[ZE[lnumber,mnumber,knumber,p,e],{lnumber,1,lmax},{mnumber,0,lnumber},{knumber,kmin,kmax}];
energyout=Total[Flatten[energyangularlist[[All,All,All,1]]]];
energyin=Total[Flatten[energyangularlist[[All,All,All,3]]]];
angularout=Total[Flatten[energyangularlist[[All,All,All,2]]]];
angularin=Total[Flatten[energyangularlist[[All,All,All,4]]]];
{energyout,angularout,energyin,angularin}
]
ELScalarFlux[p_,e_,lmax_,kmin_,kmax_]:=Module[{energyangularlist,energyout,angularout,energyin,angularin},
energyangularlist=ParallelTable[ZEscalar[lnumber,mnumber,knumber,p,e],{lnumber,0,lmax},{mnumber,0,lnumber},{knumber,kmin,kmax}];
energyout=Total[Flatten[energyangularlist[[All,All,All,1]]]];
energyin=Total[Flatten[energyangularlist[[All,All,All,3]]]];
angularout=Total[Flatten[energyangularlist[[All,All,All,2]]]];
angularin=Total[Flatten[energyangularlist[[All,All,All,4]]]];
{energyout,angularout,energyin,angularin}
]


End[];


EndPackage[];
