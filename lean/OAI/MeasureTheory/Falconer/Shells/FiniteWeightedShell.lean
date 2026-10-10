import OAI.MeasureTheory.Falconer.Shells.ContinuousCoefficientShell
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem finite_weighted_shell_square {ι : Type*} (s : Finset ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ) (w : ι → ℝ) {B : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hi : ∀ i ∈ s, Integrable (fun r => ‖F i r‖^2) μ)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (F i) μ)
    (hB : ∀ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) ≤ (w i)^2*B) :
    (∫ r, ‖∑ i ∈ s, F i r‖^2 ∂μ) ≤ (∑ i ∈ s, w i)^2*B := by
  classical
  have hz (i : ι) (his : i ∈ s) (hwi : w i = 0) :
      ∀ᵐ r ∂μ, F i r = 0 := by
    have he : (∫ r, ‖F i r‖^2 ∂μ) = 0 :=
      le_antisymm (by simpa [hwi] using hB i his)
        (integral_nonneg (fun _ => sq_nonneg _))
    have hh := (integral_eq_zero_iff_of_nonneg (fun r => sq_nonneg (‖F i r‖)) (hi i his)).mp he
    filter_upwards [hh] with r hr
    simpa using hr
  have hae : ∀ᵐ r ∂μ, ∀ i ∈ s, w i = 0 → F i r = 0 := by
    exact (eventually_all_finset s).mpr (fun i his =>
      (ae_all_iff).mpr (fun hwi => hz i his hwi))
  let G : ℝ → ℝ := fun r => ∑ i ∈ s, ‖F i r‖^2 / w i
  let W : ℝ := ∑ i ∈ s, w i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hgi : Integrable G μ := integrable_finsetSum s
    (fun i his => (hi i his).div_const (w i))
  have hpoint : ∀ᵐ r ∂μ, ‖∑ i ∈ s, F i r‖^2 ≤ W*G r := by
    filter_upwards [hae] with r hr
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s _) 2).trans
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
      (fun i his => div_nonneg (sq_nonneg _) (hw i his))
    intro i his
    by_cases hwi : w i = 0
    · simp [hwi,hr i his hwi]
    · rw [mul_div_cancel₀ _ hwi]
  have hsi : Integrable (fun r => ‖∑ i ∈ s, F i r‖^2) μ := by
    have hsm : AEStronglyMeasurable (fun r => ∑ i ∈ s, F i r) μ := by
      convert Finset.aestronglyMeasurable_sum s hm using 1
      ext r
      simp
    apply (hgi.const_mul W).mono' (hsm.norm.pow 2)
    filter_upwards [hpoint] with r hr
    change ‖‖∑ i ∈ s, F i r‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hr
  have hBi (i : ι) (his : i ∈ s) :
      (∫ r, ‖F i r‖^2 ∂μ) / w i ≤ w i*B := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · apply (div_le_iff₀ (lt_of_le_of_ne (hw i his) (Ne.symm hwi))).mpr
      nlinarith [hB i his]
  calc
    _ ≤ ∫ r, W*G r ∂μ := integral_mono_ae hsi (hgi.const_mul W) hpoint
    _ = W * ∑ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) / w i := by
      rw [integral_const_mul,integral_finsetSum s (fun i his => (hi i his).div_const (w i))]
      simp only [integral_div]
    _ ≤ W * ∑ i ∈ s, w i*B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hBi) hW
    _ = _ := by rw [← Finset.sum_mul]; dsimp [W]; ring

end PlanarFalconer

end OAI
