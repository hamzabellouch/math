import OAI.Analysis.KadisonKastler.RealNestCompletion
import OAI.Analysis.KadisonKastler.PublishedNestDistance

namespace OAI

/-! # The required real-nest distance theorem

Arveson's distance formula is proved here in the precise approximation
form used by the application. Finite contractive block completions and
weak operator compactness supply a correction with norm at most the nest
defect. No nest-distance theorem is assumed.
-/

namespace KadisonKastler

noncomputable section

universe u

theorem publishedRealNestDistance : PublishedRealNestDistance.{u} := by
  intro H _ _ _ P hP hmono T δ η hδ hη hdefect
  by_cases hzero : δ = 0
  · subst δ
    refine ⟨T, ?_, ?_⟩
    · intro a
      exact norm_eq_zero.mp (le_antisymm (hdefect a) (norm_nonneg _))
    · simpa using hη
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hzero)
  let U : H →L[ℂ] H := (δ⁻¹ : ℝ) • T
  have hU : ∀ a, ‖(1 - P a) * U * P a‖ ≤ 1 := by
    intro a
    calc
      _ = δ⁻¹ * ‖(1 - P a) * T * P a‖ := by
        simp only [U, mul_smul_comm, smul_mul_assoc, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hδpos)]
      _ ≤ δ⁻¹ * δ := mul_le_mul_of_nonneg_left (hdefect a) (inv_nonneg.mpr hδ)
      _ = 1 := inv_mul_cancel₀ hzero
  obtain ⟨X, hX, hfix⟩ := real_nest_contractive_completion P hP hmono U hU
  have hc (a : ℝ) : (1 - P a) * ((δ : ℝ) • X) * P a = (1 - P a) * T * P a := by
    simp only [mul_smul_comm, smul_mul_assoc]
    rw [hfix a]
    simp only [U, mul_smul_comm, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hzero, one_smul]
  let S := T - (δ : ℝ) • X
  refine ⟨S, ?_, ?_⟩
  · intro a
    change (1 - P a) * (T - (δ : ℝ) • X) * P a = 0
    rw [mul_sub, sub_mul, hc, sub_self]
  · have he : S - T = -((δ : ℝ) • X) := by dsimp only [S]; abel
    calc
      ‖S - T‖ = δ * ‖X‖ := by
        rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
      _ ≤ δ := by nlinarith
      _ < δ + η := lt_add_of_pos_right δ hη

end

end KadisonKastler

end OAI
