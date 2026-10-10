import OAI.NumberTheory.CubicMoment.Estimates.MellinHeightTail

namespace OAI

/-! Joining the central Mellin moment to a proved rapid tail bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_square_le_central_tail (x y : ℂ) {H : ℝ} (h : ‖x-y‖ ≤ H) :
    ‖x‖^2 ≤ 2*‖y‖^2+2*H^2 := by
  have hx : ‖x‖ ≤ ‖y‖+H := by
    calc
      _ = ‖y+(x-y)‖ := by congr 1; ring
      _ ≤ ‖y‖+‖x-y‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl h
  have hH : 0 ≤ H := (_root_.norm_nonneg _).trans h
  have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _) hx 2
  nlinarith [sq_nonneg (‖y‖-H),sq_nonneg ‖x‖]

theorem full_mellin_moment_of_central {κ : Type*} [Fintype κ]
    (f : κ → ℝ → ℂ) (hf : ∀ r, Continuous (f r)) (w : ℝ → ℂ)
    (hw : Integrable w) (A : ℕ) (hA : Integrable (fun t : ℝ => |t|^A*‖w t‖))
    {T L M : ℝ} (hT : 0 < T) (hL : 0 ≤ L) (hsize : ∀ r t, ‖f r t‖ ≤ L)
    (hcentral : (∑ r, ‖∫ t in Icc (-T) T, w t*f r t‖^2) ≤ M) :
    (∑ r, ‖∫ t, w t*f r t‖^2) ≤ 2*M+
      2*(Fintype.card κ:ℝ)*((L/T^A)*(∫ t : ℝ, |t|^A*‖w t‖))^2 := by
  let H := (L/T^A)*(∫ t : ℝ, |t|^A*‖w t‖)
  have happrox (r : κ) :
      ‖(∫ t, w t*f r t)-(∫ t in Icc (-T) T, w t*f r t)‖ ≤ H := by
    have hi : Integrable (fun t => w t*f r t) := (hw.norm.mul_const L).mono'
      (hw.aestronglyMeasurable.mul (hf r).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hsize r t) (_root_.norm_nonneg _)))
    rw [← integral_add_compl measurableSet_Icc hi,add_sub_cancel_left]
    exact bounded_product_height_tail w (f r) hw A hA hT hL (hsize r)
  calc
    _ ≤ ∑ r, (2*‖∫ t in Icc (-T) T, w t*f r t‖^2+2*H^2) :=
      Finset.sum_le_sum (fun r _ => norm_square_le_central_tail _ _ (happrox r))
    _ = 2*(∑ r, ‖∫ t in Icc (-T) T, w t*f r t‖^2)+2*(Fintype.card κ:ℝ)*H^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ _ := by dsimp [H]; nlinarith

end CubicFirstMoment

end

end OAI
