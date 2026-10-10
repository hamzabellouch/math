import OAI.NumberTheory.DirichletL.Descent.CanonicalLongKeys
import OAI.NumberTheory.DirichletL.Descent.CanonicalLongIntegral

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation
local notation "O"=>ActualEisensteinCubic.O

theorem actual_marked_bin_uniform_test
    (a₀ b₀:ℝ)(ha₀:0<a₀)(hb₀:0≤b₀)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤CanonicalCubeSeparation.columnWindowRadius a₀ b₀ → Vlog x=1)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ → ℂ) ∧ HasCompactSupport (ω₁₂:ℝ → ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂₂:ℝ → ℂ) ∧
      tsupport (ω₁₁:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
      ∃Ccoef C:ℝ,0<Ccoef ∧ 0≤C ∧
    ∀(test:ℝ → ℂ)(hs₀:Function.support test⊆Set.Icc a₀ b₀)(hTest:ContDiff ℝ ∞ test),
    ∀{σ:Type}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P),
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let p:=poolPrimary F;
      let hp:=poolPrimary_ne_zero F hF;
      let hcop:=poolPrimary_coprime F hF;
      let hg:=poolPrimary_good F hF;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      ∀(Q:Finset (primePool F →₀ ℕ))(labels:Finset (Ideal O))(Ψ:O →* ℂ)(m:O)
        (slots:Finset σ)(lists:σ → Finset (primePool F))(weights:σ → primePool F → ℂ)
        (Z M r ell V H₀ pi epschild A loss lossFinal:ℝ),
        2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 0≤M → r+3*ell+V≤Lcap → M≤Lcap →
        0≤ell → 0≤V → -eta≤r → Real.exp Alog≤Z^eta →
        (∀v∈Q,Z^ell≤(Ideal.absNorm (cubeIdeal F v):ℝ)) →
        (∀v∈Q,(Ideal.absNorm (cubeIdeal F v):ℝ)≤Real.exp 1*Z^ell) →
        r≤Lcap → ell≤Lcap → V≤Lcap → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
        em*(20*(3*Lcap+16)+30)≤pi/4 → ed*(20*(3*Lcap+16)+30)≤pi/4 →
        0≤epschild → -saving≤r+3*ell+V+48*eta+tau+pi+epschild+epsSecond →
        48*eta+tau+pi+epschild+epsSecond≤loss → slots.card≤K →
        M-ell≤r+3*ell+V → 3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal →
        loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤r+3*ell+V+lossFinal →
        (∀u,‖Ψ u‖≤1) → 0≤A → (∀I∈labels,Squarefree I) → (∀I∈labels,I≠0) →
        (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
        (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) →
        b₀*Z^(r+3*ell)≤D →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
            Z M r ell V eta tau window bw epschild A K degree) →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
            Z M r ell V eta tau window bw epschild A K degree) →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z
          test (Z^(r+3*ell)) H₀ slots lists weights) (Z^M)≤
          C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
            (∫ξ:ℝ,‖reopeningCoefficient test a₀ b₀ ha₀ hs₀ hTest ξ‖*(1+|ξ|)^(InverseClippingProfiles.momentOrder (firstDegree degree)))^2 := by
  let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox
  have hs:Function.support om⊆Set.Icc (Real.exp (-Alog)) (Real.exp Alog):=
    fun x hx=>radialFromLog_support Vlog (Vlog.smooth ⊤) Alog hbox x hx
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    actual_long_parent_energy om (Real.exp (-Alog)) (Real.exp Alog) (Real.exp_pos _) hs
      Lcap eta tau saving em ed hcap (Real.exp_pos _).le heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,C,hCcoef,hC,hparent⟩:=he epsFirst epsSecond hepsF hepsS degree
  let d:=InverseClippingProfiles.momentOrder (firstDegree degree)
  refine ⟨Ccoef,C,hCcoef,hC,?_⟩
  intro test hs₀ hTest
  let moment:ℝ:=∫ξ:ℝ,‖reopeningCoefficient test a₀ b₀ ha₀ hs₀ hTest ξ‖*(1+|ξ|)^d
  intro σ _ S D hbad hSp
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  intro Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbin hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hz:0<Z:=by linarith
  have hg' : ∀i:primePool F,goodLambda∉Ideal.span {poolPrimary F i}:=poolPrimary_good F hF
  have hinj:Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j hij
    exact Subtype.ext (by simpa only [poolPrimary_span F hF] using hij)
  have hpr (i:primePool F):goodLambda^2∣poolPrimary F i-1:=
    (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2
  let Gamma:=Ccoef*(Real.exp 1*Z^ell)^epsFirst
  let E:=C*Gamma^2*(1+A)*Z^(r+3*ell+V+lossFinal)
  have hE:0≤E:=by dsimp [E];positivity
  refine (actual_long_bin_normalized_energy S D hbad hSp Q labels Ψ m test a₀ b₀ ha₀ hb₀ hs₀ hTest
    Vlog hone Z r ell V H₀ (Z^M) E d hz hD (Real.rpow_pos_of_pos hz _) hE hQlo hQhi slots lists weights ?_).trans_eq ?_
  · intro ξ
    have hbnd:=hparent (poolPrimary F) (poolPrimary_ne_zero F hF) hg' hinj
      (poolPrimary_coprime F hF) (poolPrimary_odd F hF) hpr Finset.univ Q labels Ψ m (m*excludedGenerator S)
      slots lists weights Z M r ell V H₀ ξ pi epschild A loss lossFinal
      hZ hbin hbinExp hM hFcap hMcap hell hV hr hbZ (fun _ _=>Finset.subset_univ _)
      (by intro v hv;rw [cubeIdeal_primeProduct_norm F hF];exact hQlo v hv)
      (by intro v hv;rw [cubeIdeal_primeProduct_norm F hF];exact hQhi v hv)
      hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
      hΨ hA hsf hn hlabels hslots hweights (hleft ξ) (hright ξ)
    have hc (I:Ideal O) := funext (actualLongCoefficient_complete S D hbad Ψ m H₀ (Z^ell) ξ I)
    have hrow: (fun I z=>varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) hg' Finset.univ Q
        (separatedCubeCoefficient (fun v=>reopenedCubeCoefficient H₀
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v))
          (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) (Z^ell) ξ) Ψ m (idealGenerator I)
        (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist Vlog ξ (columnLog (poolPrimary F) (Z^r) T)) z)=
      (fun I z=>varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) hg' Finset.univ Q
        (separatedCubeCoefficient (fun v=>reopenedCubeCoefficient H₀
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v))
          (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) (Z^ell) ξ) Ψ m (idealGenerator I)
        (fun v T=>primeMark slots lists weights (v.support∪T)*normTwistedSource om ξ (primeProductNorm (poolPrimary F) T/Z^r)) z) := by
      funext I z
      exact long_marked_source_eq (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        hg' Finset.univ Q _ Ψ m (idealGenerator I) z slots lists weights Vlog Alog hbox Z r ξ hz
    rw [hrow]
    convert hbnd using 1
    · apply congrArg (fun f => Z^(-r-2*ell-V)*rowFamilyEnergy labels f (Z^M))
      funext I z
      exact congrArg (fun coeff => varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) hg' Finset.univ Q coeff Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (v.support∪T)*normTwistedSource om ξ
          (primeProductNorm (poolPrimary F) T/Z^r)) z) (hc I).symm
    · dsimp [E,Gamma,d]
      try simp only [Real.norm_eq_abs]
      ring
  · dsimp [E,Gamma,moment]

end SevenEighths.InverseMoment

end

end OAI
