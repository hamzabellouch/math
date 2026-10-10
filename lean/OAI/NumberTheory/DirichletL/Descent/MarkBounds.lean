import OAI.NumberTheory.DirichletL.Descent.IdealMasks

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

 theorem finite_primeSupport_card {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (U : Finset ι) :
    (IdealMobiusDivisorSum.primeSupport (Ideal.span {∏ i ∈ U, p i})).card = U.card := by
  have hc : Pairwise (Function.onFun IsCoprime (fun i : U => Ideal.span {p i.val})) := by
    intro i j hij
    exact hcop (fun he => hij (Subtype.ext he))
  have he := Fintype.card_congr (productPrimeIndexEquiv (fun i : U => p i.val) hc)
  simpa only [Finset.prod_coe_sort, PrimeIndex, Fintype.card_coe, CompletedGauss.primeSupport, IdealMobiusDivisorSum.primeSupport] using he.symm

theorem finite_primeMark_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ U : Finset ι,
      ‖primeMark slots lists a U‖ ≤ C * (primeProductNorm p U)^ε := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha U
  have hI : (Ideal.span {∏ i ∈ U, p i} : Ideal Eis) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  have hh := hb (Ideal.span {∏ i ∈ U, p i}) hI
  rw [finite_primeSupport_card p hcop U] at hh
  have hn : (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) = primeProductNorm p U :=
    (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span _).symm
  rw [hn] at hh
  exact (primeMark_norm_le_divisor_count slots lists a U hslots ha).trans hh

theorem finite_primeMark_extracted_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ A U : Finset ι,
      ‖primeMark slots lists a (A ∪ U)‖ ≤ (2:ℝ)^A.card * C * (primeProductNorm p U)^ε := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A U
  have hI : (Ideal.span {∏ i ∈ U, p i} : Ideal Eis) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  have hh := hb (Ideal.span {∏ i ∈ U, p i}) hI
  rw [finite_primeSupport_card p hcop U] at hh
  have hn : (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) = primeProductNorm p U :=
    (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span _).symm
  rw [hn] at hh
  calc
    _ ≤ (2:ℝ)^(A ∪ U).card := primeMark_norm_le_divisor_count _ _ _ _ hslots ha
    _ ≤ (2:ℝ)^(A.card+U.card) := pow_le_pow_right₀ (by norm_num) (Finset.card_union_le _ _)
    _ = (2:ℝ)^A.card * (2:ℝ)^U.card := pow_add _ _ _
    _ ≤ (2:ℝ)^A.card * (C * (primeProductNorm p U)^ε) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
