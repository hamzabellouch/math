import OAI.NumberTheory.DirichletL.Descent.FirstMarkedColumns

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_marked_zero_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ L K : ℝ),0≤G₁ → 0≤G₂ → 0≤L →
      (∀ U,‖test₁ U‖≤G₁) → (∀ U,‖test₂ U‖≤G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤L) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤L) →
      ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
        (wholeMarkedTest slots lists a test₁) (wholeMarkedTest slots lists a test₂) W K‖ ≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (Cm*L^ε*G₁)*(Cm*L^ε*G₂) * |K| * ‖paperRadialFourier W 0‖ else 0 := by
  obtain ⟨Cm,hCm,hmark⟩ := whole_marked_test_uniform ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f slots lists a hslots ha
    test₁ test₂ W G₁ G₂ L K hG₁ hG₂ hL ht₁ ht₂ hs₁ hs₂
  apply (canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hmark p hp hcop slots lists a hslots ha test₁ G₁ L hG₁ hL ht₁ hs₁ _)
        (hmark p hp hcop slots lists a hslots ha test₂ G₂ L hG₂ hL ht₂ hs₂ _)
        (norm_nonneg _) (by positivity)) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

end
end SevenEighths.InverseMoment

end OAI
