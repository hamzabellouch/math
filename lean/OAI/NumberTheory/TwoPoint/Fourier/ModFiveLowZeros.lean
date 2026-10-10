import OAI.NumberTheory.TwoPoint.Fourier.ModFiveHighZeros
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Compact-height completion of the fixed-modulus zero-free strip.
The compactness step is simultaneous for the finite family of characters,
using the already proved nonvanishing on the line `Re s = 1`.
-/

namespace TwoPointCorrelations

open Complex Set Metric
open scoped Classical

lemma modFive_compact_height_zero_free (T : ℝ) : ∃ r : ℝ, 0 < r ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ s : ℂ,
      1 - r ≤ s.re → |s.im| ≤ T → DirichletCharacter.LFunction χ s ≠ 0 := by
  let K : Set ℂ := (fun t : ℝ => (1 : ℂ) + Complex.I * (t : ℂ)) '' Icc (-T) T
  let U : Set ℂ := ⋂ χ : DirichletCharacter ℂ 5,
    if χ = 1 then univ else {s | DirichletCharacter.LFunction χ s ≠ 0}
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro χ
    by_cases hχ : χ = 1
    · simp only [hχ, ite_true, isOpen_univ]
    · simp only [hχ, ite_false]
      exact isOpen_ne_fun (DirichletCharacter.differentiable_LFunction hχ).continuous
        continuous_const
  have hKU : K ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    apply mem_iInter.mpr
    intro χ
    by_cases hχ : χ = 1
    · simp only [hχ, ite_true, mem_univ]
    · simp only [hχ, ite_false, mem_ofPred_eq]
      exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simp)
  obtain ⟨r, hr, hrU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro χ hχ s hs ht
  by_cases hs1 : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hs1
  · have hs1' : s.re < 1 := lt_of_not_ge hs1
    have hp : (1 : ℂ) + Complex.I * (s.im : ℂ) ∈ K :=
      ⟨s.im, abs_le.mp ht, rfl⟩
    have hdist : dist s ((1 : ℂ) + Complex.I * (s.im : ℂ)) < r := by
      have heq : s - ((1 : ℂ) + Complex.I * (s.im : ℂ)) = ((s.re - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (sub_neg.mpr hs1')]
      linarith
    have hmem : s ∈ U := hrU (mem_thickening_iff.mpr ⟨_, hp, hdist⟩)
    have h := mem_iInter.mp hmem χ
    simpa only [hχ, ite_false, mem_ofPred_eq] using h

/-- The full fixed-modulus logarithmic zero-free region, including bounded
heights. Its constant is uniform across the three nonprincipal characters. -/
theorem modFive_nonprincipal_zero_free : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ (t β : ℝ),
      1 - c / Real.log (|t| + 2) ≤ β →
      DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  obtain ⟨c, hc, T, hT, hhigh⟩ := modFive_nonprincipal_high_zero_free
  obtain ⟨r, hr, hlow⟩ := modFive_compact_height_zero_free T
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min c (r * Real.log 2), lt_min hc (mul_pos hr hlog2), ?_⟩
  intro χ hχ t β hβ
  have hH : 0 < Real.log (|t| + 2) := modFive_log_height_pos t
  by_cases ht : T ≤ |t|
  · apply hhigh χ hχ t β ht
    have hdiv := div_le_div_of_nonneg_right (min_le_left c (r * Real.log 2)) hH.le
    linarith
  · apply hlow χ hχ ((β : ℂ) + Complex.I * (t : ℂ))
    · have hlog : Real.log 2 ≤ Real.log (|t| + 2) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
      have hdiv : min c (r * Real.log 2) / Real.log (|t| + 2) ≤ r := by
        apply (div_le_iff₀ hH).mpr
        exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hlog hr.le)
      simpa using (show 1 - r ≤ β by linarith)
    · simpa using (le_of_lt (lt_of_not_ge ht))

end TwoPointCorrelations

end OAI
