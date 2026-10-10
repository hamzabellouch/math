import OAI.NumberTheory.DirichletL.Descent.FirstLiveExponentCaps
import OAI.NumberTheory.DirichletL.Descent.FirstLiveColumnScale
import OAI.NumberTheory.DirichletL.Descent.FirstLiveRadiusPositive
import OAI.NumberTheory.DirichletL.Descent.FirstStepScalarCaps
import OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStep

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

lemma columnScale_physical (Z r:ℝ)(hZ:1<Z)(k:SourceIndex)(l:ℕ)(negative:Bool):
    columnScale Z r k l negative=physicalScales (Z^r) k l (if negative then 7 else 8):=by
  rw [physicalScales_rpow Z r hZ k l]
  cases negative <;> rfl

 theorem original_live_step_scalars {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
    (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(om:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (K Z M r ell V F eta tau theta oldb b window em ed pi:ℝ)
    (hZ:1<Z)(hbin:2≤Z^eta)(hF:0≤F)(hM:0≤M)(hMF:M≤F)
    (hr: -eta≤r)(hrF:r≤F)(hell:0≤ell)(hellF:ell≤F)(hV:0≤V)(hVF:V≤F)
    (heta:0≤eta)(heta1:eta≤1)(htau:0≤tau)(htau1:tau≤1)
    (hwindow:Real.exp window≤Z^eta)(hold:oldb≤Real.exp window)(hb:b≤Real.exp window)
    (hem:0≤em)(hed:0≤ed)(hpi:0≤pi)(hetapi:6*eta≤pi)
    (hsmall:em*(20*(3*F+16)+30)≤pi/4)(hsmall':ed*(20*(3*F+16)+30)≤pi/4)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hlabels:∀I∈labels,I≠0)(hs:∀y,om y≠0→y≤oldb):
    let A:=3*F+16;
    let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
    let W:=fun y=>normTwistedSource om theta (y/Z^r);
    let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
    ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),∀negative:Bool,
      let X:=columnScale Z r k.1 k.2.1 negative;
      let Y:=firstCellRadius Z M r ell V eta tau k.1 k.2.2;
      1≤Y ∧ 1≤X*Real.exp window ∧ X*Real.exp window≤Z^(A+1) ∧ Y≤Z^(16*A+20) ∧ Y⁻¹≤Z^(4*A+2) ∧
      b*X≤Z^(16*A+20) ∧ exponent Z (k.1 3)+eta+2*(A+1)+tau+(4*A+2)≤16*A+20 ∧
      firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4))+
        (9/2:ℝ)*eta≤16*A+20 ∧
      em*(ell+exponent Z (k.1 4)/2+exponent Z k.2.1+(16*A+20)+11*eta/2)≤pi ∧
      em*(r-columnA Z k.1 negative-exponent Z (k.1 2)-exponent Z k.2.1)+7*eta/2+
        ed*(3*ell+exponent Z (k.1 2)+exponent Z k.2.1+5*eta)+
        2*em*(2*ell+exponent Z (k.1 2)+exponent Z k.2.1+4*eta)≤pi+eta/2 ∧
      ell+eta≤16*A+20 ∧ exponent Z (k.1 4)+eta≤16*A+20 ∧
      exponent Z (k.1 2)+eta≤16*A+20 ∧ exponent Z k.2.1+eta≤16*A+20:=by
  intro A cutoff W S k hk negative X Y
  have hz:0<Z:=zero_lt_one.trans hZ
  have hA:0≤A:=by dsimp [A];linarith
  have hFA:F≤A:=by dsimp [A];linarith
  obtain ⟨hcoords,ht,hj⟩:=original_live_exponent_caps p hp hcop hg pool Q labels β cutoff Ψ m mark om Φ K Z r ell F eta tau theta oldb
    hZ hbin hF hrF hellF heta htau (hold.trans hwindow) hQ hlabels hs k hk
  have hecap:3*F+15*eta+tau≤A:=by dsimp [A];linarith
  have hkcap:∀i,0≤exponent Z (k.1 i) ∧ exponent Z (k.1 i)≤A:=fun i=>⟨(hcoords i).1,(hcoords i).2.trans hecap⟩
  have hacap:0≤columnA Z k.1 negative ∧ columnA Z k.1 negative≤A:=hkcap (if negative then 0 else 1)
  have htcap:exponent Z k.2.1≤A:=ht.2.trans hecap
  have hjcap:exponent Z k.2.2≤A:=hj.2.trans hecap
  have hscl:=first_step_scalar_caps Z A M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative)
    (exponent Z (k.1 2)) (exponent Z (k.1 4)) (exponent Z k.2.1) (exponent Z k.2.2) eta tau window b
    hZ hA hM (hMF.trans hFA) (by linarith) (hrF.trans hFA) hell (hellF.trans hFA) hV (hVF.trans hFA)
    (hkcap 3).1 (hkcap 3).2 hacap.1 hacap.2 (hkcap 2).1 (hkcap 2).2 (hkcap 4).1 (hkcap 4).2
    ht.1 htcap hj.1 hjcap heta heta1 htau htau1 hwindow (hb.trans hwindow)
  have hloss:=first_step_scalar_losses A r ell (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4))
    (exponent Z k.2.1) eta pi em ed hA (hrF.trans hFA) (hellF.trans hFA) hacap.1 (hkcap 2).1 (hkcap 2).2
    (hkcap 4).2 ht.1 htcap heta heta1 hem hed hpi hetapi hsmall hsmall'
  have hYone:=first_live_cell_radius_one p hp hcop hg pool Q labels _ Z M r ell V eta tau β Ψ m mark W Φ K hlabels k hk
  have hW:∀y,W y≠0→y≤oldb*Z^r:=by
    intro y hy
    have hnon:om (y/Z^r)≠0:=by intro h;exact hy (by simp [W,normTwistedSource,h])
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hnon)
  have hcol:=original_live_column_scale p hp hcop hg pool Q labels _ β cutoff Ψ m mark W Φ K (Z^r) oldb
    (Real.rpow_pos_of_pos hz _) hW k hk
  have hXone:1≤X*Real.exp window:=by
    have hpos:0≤X:=Real.rpow_nonneg hz.le _
    apply le_trans _ (mul_le_mul_of_nonneg_left hold hpos)
    dsimp [X]
    rw [columnScale_physical Z r hZ]
    cases negative
    · exact hcol.2
    · exact hcol.1
  refine ⟨hYone,hXone,hscl.1,hscl.2.1,hscl.2.2.1,hscl.2.2.2.1,hscl.2.2.2.2.1,
    hscl.2.2.2.2.2.1,hloss.1,hloss.2,?_,?_,?_,?_⟩ <;> linarith [(hkcap 4).2,(hkcap 2).2]

end SevenEighths.InverseMoment

end

end OAI
