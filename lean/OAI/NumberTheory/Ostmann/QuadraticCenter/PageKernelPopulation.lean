import OAI.NumberTheory.Ostmann.QuadraticCenter.PageKernelExclusion

namespace OAI

/-! # Population cost of deleting the large Page-kernel family -/

namespace Ostmann

/-- The threshold R replaces the actual exceptional conductor uniformly.
At R=(log X)^100 the leading cost is X/(log X)^50. -/
theorem exists_page_kernel_population_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : PublishedProgressionInput) (Q₀ : ℕ) (R : ℝ)
      (S T : Finset ℤ) (f g : ℤ → ℤ) (r s : ℤ → ℕ) (m : ℕ) (h : ℤ) (X : ℝ),
      0 < R → 0 < m → 0 ≤ X →
      (∀ x ∈ S, f x ≠ 0) → (∀ y ∈ T, g y ≠ 0) →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ y ∈ T, g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs) →
      (((S.product T).filter fun z => f z.1 * g z.2 ∈ pageKernelExclusion P Q₀ R).card : ℝ) ≤
        C * (X / Real.sqrt R + 2 * Real.sqrt (X * m) + m) := by
  obtain ⟨C, hC, hbound⟩ := exists_exceptional_kernel_family_bound
  refine ⟨C, hC, ?_⟩
  intro P Q₀ R S T f g r s m h X hR hm hX hf hg hred hr hs hspanS hspanT hcross
  apply page_kernel_exclusion_count P Q₀ R _ S T f g (by positivity)
  intro q hq
  have hqpos : 0 < q := by
    have hh : (0 : ℝ) < q := hR.trans hq
    exact_mod_cast hh
  have hb := hbound S T f g r s m q h X hm hqpos hX hf hg hred hr hs hspanS hspanT hcross
  have hquot : X / Real.sqrt (q : ℝ) ≤ X / Real.sqrt R :=
    div_le_div_of_nonneg_left hX (Real.sqrt_pos.mpr hR) (Real.sqrt_le_sqrt hq.le)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  linarith

end Ostmann

end OAI
