import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.MomentBounds
import OAI.Probability.BinarySweep.Analytic.OneAxis

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma oneAxis_gridWeight_affine (bits : Fin 1 → ℕ) (z : ℝ) (g : GridChoices bits) :
    gridWeight bits z g = (1-z)*gridWeight bits 0 g + z*gridWeight bits 1 g := by
  simp only [oneAxis_gridWeight, lineLaw]
  ring

lemma oneAxis_gridWeight_one_nonneg (bits : Fin 1 → ℕ) (g : GridChoices bits) :
    0 ≤ gridWeight bits 1 g := by
  simp only [oneAxis_gridWeight, lineLaw, sub_self, zero_mul, one_mul, zero_add]
  exact finiteLaw_nonneg (binarySweep _) _

lemma oneAxis_conditional_norm_le_z_div {h D : ℕ} {bits : Fin 1 → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) (hD : 1 < D) :
    ‖conditionalOperator H z ρ‖ ≤ z / conditionalNormalizer H z := by
  have hZ := conditionalNormalizer_pos H hz hz1
  apply (conditionalOperator H z ρ).opNorm_le_bound (div_nonneg hz hZ.le)
  intro x
  let F (w : ℝ) : RepSpace D := ∑ g : GridChoices bits, if hg : pathEvent H g then
    (gridWeight bits w g : ℂ) • ρ (remainingPerm H g hg) x else 0
  have hF0 : F 0 = 0 := by
    have he := congrArg (fun K : RepSpace D →L[ℂ] RepSpace D => K x)
      (oneAxis_conditionalOperator_zero H ρ hD)
    rw [conditionalOperator_apply] at he
    change (conditionalNormalizer H 0 : ℂ)⁻¹ • F 0 = 0 at he
    exact (smul_eq_zero.mp he).resolve_left (inv_ne_zero (by
      exact_mod_cast (conditionalNormalizer_pos H (by norm_num : (0 : ℝ) ≤ 0)
        (by norm_num : (0 : ℝ) < 1)).ne'))
  have hFz : F z = (z : ℂ) • F 1 := by
    have hl : F z = ((1-z : ℝ) : ℂ) • F 0 + (z : ℂ) • F 1 := by
      simp only [F, Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : pathEvent H g
      · simp only [dite_eq_left hg, oneAxis_gridWeight_affine bits z g,
          Complex.ofReal_add, Complex.ofReal_mul, add_smul, mul_smul]
      · simp only [dite_eq_right hg, smul_zero, add_zero]
    simpa only [hF0, smul_zero, zero_add] using hl
  have hF1 : ‖F 1‖ ≤ ‖x‖ := by
    calc
      _ ≤ ∑ g : GridChoices bits, ‖if hg : pathEvent H g then
        (gridWeight bits 1 g : ℂ) • ρ (remainingPerm H g hg) x else 0‖ := norm_sum_le _ _
      _ ≤ ∑ g : GridChoices bits, gridWeight bits 1 g * ‖x‖ := by
        apply Finset.sum_le_sum
        intro g _
        by_cases hg : pathEvent H g
        · simp only [dite_eq_left hg, norm_smul, hρ (remainingPerm H g hg) x, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (oneAxis_gridWeight_one_nonneg bits g), le_refl]
        · simp only [dite_eq_right hg, norm_zero]
          exact mul_nonneg (oneAxis_gridWeight_one_nonneg bits g) (norm_nonneg _)
      _ = ‖x‖ := by rw [← Finset.sum_mul, gridWeight_sum, one_mul]
  rw [conditionalOperator_apply]
  change ‖(conditionalNormalizer H z : ℂ)⁻¹ • F z‖ ≤ _
  rw [hFz, norm_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hZ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
  calc
    _ ≤ (conditionalNormalizer H z)⁻¹ * (z * ‖x‖) := by gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

lemma oneAxis_normalizer_lower {h : ℕ} {bits : Fin 1 → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1/2) :
    (2 * ((gridSize bits).factorial : ℝ))⁻¹ ≤ conditionalNormalizer H z := by
  have hz1 : z < 1 := by linarith
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  have hu : (Fintype.card (Equiv.Perm (GridSlot bits)) : ℝ)⁻¹ =
      ((gridSize bits).factorial : ℝ)⁻¹ := by rw [Fintype.card_perm, card_gridSlot]
  calc
    _ = (1/2 : ℝ) * (Fintype.card (Equiv.Perm (GridSlot bits)) : ℝ)⁻¹ := by
      rw [hu, mul_inv_rev]; ring
    _ ≤ gridWeight bits z g := by
      rw [oneAxis_gridWeight_affine, oneAxis_gridWeight_zero]
      have hp := mul_nonneg hz (oneAxis_gridWeight_one_nonneg bits g)
      have hn : 0 ≤ (Fintype.card (Equiv.Perm (GridSlot bits)) : ℝ)⁻¹ := by positivity
      nlinarith
    _ ≤ conditionalNormalizer H z := by
      unfold conditionalNormalizer
      have he := Finset.single_le_sum (fun (g' : GridChoices bits) _ =>
        show 0 ≤ if pathEvent H g' then gridWeight bits z g' else 0 by
          split_ifs <;> first | exact (gridWeight_pos bits hz hz1 g').le | exact le_rfl)
        (Finset.mem_univ g)
      simpa only [ite_eq_left hg] using he

theorem oneAxis_conditional_norm_le {h D : ℕ} {bits : Fin 1 → ℕ}
    (H : PathFamily bits h) {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1/2)
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D))
    [ρ.IsIrreducible] (hρ : IsUnitaryRep ρ) (hD : 1 < D) :
    ‖conditionalOperator H z ρ‖ ≤ 2 * ((gridSize bits).factorial : ℝ) * z := by
  have hz1 : z < 1 := by linarith
  have hb := oneAxis_normalizer_lower H hz hzhalf
  have hF : (0 : ℝ) < 2 * ((gridSize bits).factorial : ℝ) := by positivity
  calc
    _ ≤ z / conditionalNormalizer H z := oneAxis_conditional_norm_le_z_div H hz hz1 ρ hρ hD
    _ ≤ z / (2 * ((gridSize bits).factorial : ℝ))⁻¹ :=
      div_le_div_of_nonneg_left hz (inv_pos.mpr hF) hb
    _ = _ := by rw [div_inv_eq_mul]; ring

end BinaryCoordinateSweeps

end

end OAI
