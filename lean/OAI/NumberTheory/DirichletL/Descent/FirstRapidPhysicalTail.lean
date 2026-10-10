import OAI.NumberTheory.DirichletL.Descent.FirstTailAggregation
import OAI.NumberTheory.DirichletL.Descent.FirstSourceTail

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem first_whole_cube_rapid_physical_tail (ε:ℝ) (hε:0<ε)
    (Mmax Fmax eta tau saving:ℝ) (hMm:0≤Mmax) (hFm:0≤Fmax)
    (heta:0≤eta) (htau:0<tau) :
    ∃ (s:Finset (ℕ×ℕ)) (Ct Cm:ℝ),0<Ct ∧ 0<Cm ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι) (C D extra₁ extra₂:Finset ι)
      (f:Ideal O) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (test₁ test₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (E G₁ G₂ Z M r ell V B j:ℝ) (delta:Finset ι→ℝ),
      b.Admissible → Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      f≠0 → 0≤E → 0≤G₁ → 0≤G₂ → 1≤Z → 0≤M → M≤Mmax →
      0≤ell → 0≤V → -eta≤r → r+3*ell+V≤Fmax →
      primeProductNorm p C≤Z^(r+eta) →
      primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖test₁ U‖≤G₁) → (∀U,‖test₂ U‖≤G₂) →
      (∀U,test₁ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      (∀U,test₂ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f:ℝ)≤Z^(V+eta) → primeProductNorm p D≤Z^(delta D+eta) →
      Z^(B-eta)≤primeProductNorm p C →
      Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2 →
      ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U) W (Z^M)
        (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent
          b.rightExponent b.leftBit b.rightBit f)
          (Z^(firstPhysicalHeight M r ell V (delta D) B j+12*eta+tau))) D‖≤
      65536*(Cm*(E*Z^(r+eta))^ε*G₁)*(Cm*(E*Z^(r+eta))^ε*G₂)*
        (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  obtain ⟨order,horder⟩:=choose_actual_first_tail_order Mmax Fmax eta tau saving hMm hFm heta htau
  obtain ⟨s,Ct,Cm,hCt,hCm,htail⟩:=first_whole_cube_canonical_tail ε hε order
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C D extra₁ extra₂ f Ψ₁ Ψ₂ m₁ m₂ slots lists a
    test₁ test₂ W E G₁ G₂ Z M r ell V B j delta hb hCB hD hf hE hG₁ hG₂ hZ hM hMmax
    hell hV hr hwhole hC he₁ he₂ hΨ₁ hΨ₂ hslots ha ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlocal:=htail p hp hinj hcop hg hc pool b hb C D hCB f hf Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V
    (delta D) B j eta tau hG₁ hG₂ hz ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  dsimp only at hlocal
  apply hlocal.trans
  exact horder p hp b C D hCB hD Z M r ell V
    (Cm*(E*Z^(r+eta))^ε*G₁) (Cm*(E*Z^(r+eta))^ε*G₂)
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hM hMmax hell hV hr hwhole (by positivity) (by positivity) (by positivity) hb₁ hb₂ hC

end SevenEighths.InverseMoment

end

end OAI
