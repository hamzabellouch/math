import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneLineDerivatives
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTailShift

namespace OAI

/-! The scalar tail and a third-derivative bound force
second directional derivatives to have an integrable square envelope. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory
open scoped ContDiff

def derivativeTail (x : Plane) : ℝ := (planeTailProfile x) ^ (1 / 3 : ℝ)

theorem derivativeTail_pos (x : Plane) : 0 < derivativeTail x :=
  Real.rpow_pos_of_pos (planeTailProfile_pos x) _

theorem derivativeTail_le_one (x : Plane) : derivativeTail x ≤ 1 :=
  Real.rpow_le_one (planeTailProfile_pos x).le (planeTailProfile_le_one x) (by norm_num)

theorem derivativeTail_cube (x : Plane) : derivativeTail x ^ 3 = planeTailProfile x := by
  unfold derivativeTail
  rw [← Real.rpow_natCast, ← Real.rpow_mul (planeTailProfile_pos x).le]
  norm_num

theorem derivativeTail_continuous : Continuous derivativeTail :=
  planeTailProfile_smooth.continuous.rpow_const (fun x => Or.inl (planeTailProfile_pos x).ne')

theorem derivativeTail_square_integrable : Integrable (fun x => derivativeTail x ^ 2) := by
  have hi : Integrable (fun x : Plane => (1 + ‖x‖ ^ 2) ^ (-(8 / 3 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simp [Plane]; norm_num)
  have he (x : Plane) : derivativeTail x ^ 2 = planeBarrierSquare x ^ (-(4 / 3 : ℝ)) := by
    have hp : planeTailProfile x = planeBarrierSquare x ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
      rfl
    unfold derivativeTail
    rw [hp, ← Real.rpow_natCast,
      ← Real.rpow_mul (Real.rpow_nonneg (planeBarrierSquare_pos x).le _),
      ← Real.rpow_mul (planeBarrierSquare_pos x).le]
    norm_num
  apply hi.mono' (derivativeTail_continuous.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  change ‖derivativeTail x ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), he]
  have hpow := Real.rpow_le_rpow_of_nonpos
    (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2)
    (planeBarrierSquare_norm_sq x) (by norm_num : -(4 / 3 : ℝ) ≤ 0)
  convert hpow using 1
  norm_num

theorem scalar_second_directional_tail {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ y, |f y| ≤ B * planeTailProfile y)
    (hfM : ∀ y, ‖iteratedFDeriv ℝ 3 f y‖ ≤ M)
    (x v : Plane) (hv : ‖v‖ ≤ 1) :
    |iteratedFDeriv ℝ 2 f x (fun _ => v)| ≤ (100 * B + M) * derivativeTail x := by
  let h := derivativeTail x
  have hh : 0 < h := derivativeTail_pos x
  have hh1 : h ≤ 1 := derivativeTail_le_one x
  have hline (t : ℝ) : |iteratedDeriv 3 (scalarLine f x v) t| ≤ M := by
    have ht := scalarLine_iteratedDeriv_bound hf x v 3 hfM t
    have hp : ‖v‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg v) hv
    exact ht.trans (by nlinarith)
  have hb (t : ℝ) (ht : |t| ≤ 1) :
      |scalarLine f x v t| ≤ 25 * B * planeTailProfile x := by
    have hs := mul_le_mul_of_nonneg_left (planeTailProfile_line_le x v ht hv) hB
    exact (hfB _).trans (by nlinarith [hs])
  have he := second_derivative_three_point_bound (scalarLine_smooth hf x v) hh hM hline
    (hb 0 (by norm_num)) (hb h (by simpa only [abs_of_pos hh] using hh1))
    (hb (-h) (by simpa only [abs_neg, abs_of_pos hh] using hh1))
  have hc : h ^ 3 = planeTailProfile x := derivativeTail_cube x
  have hd : iteratedDeriv 2 (scalarLine f x v) 0 =
      iteratedFDeriv ℝ 2 f x (fun _ => v) := by
    simpa only [zero_smul, add_zero] using scalarLine_iteratedDeriv hf x v 2 0
  rw [hd] at he
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hh)).mp
  calc
    _ ≤ 4 * (25 * B * planeTailProfile x) + M * h ^ 3 := he
    _ = ((100 * B + M) * derivativeTail x) * h ^ 2 := by rw [← hc]; dsimp [h]; ring


theorem scalar_first_directional_tail {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ y, |f y| ≤ B * planeTailProfile y)
    (hfM : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M)
    (x v : Plane) (hv : ‖v‖ ≤ 1) :
    |iteratedFDeriv ℝ 1 f x (fun _ => v)| ≤ (50 * B + M) * derivativeTail x := by
  let h := derivativeTail x
  have hh : 0 < h := derivativeTail_pos x
  have hh1 : h ≤ 1 := derivativeTail_le_one x
  have hline (t : ℝ) : |iteratedDeriv 2 (scalarLine f x v) t| ≤ M := by
    have ht := scalarLine_iteratedDeriv_bound hf x v 2 hfM t
    have hp : ‖v‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg v) hv
    exact ht.trans (by nlinarith)
  have hb (t : ℝ) (ht : |t| ≤ 1) :
      |scalarLine f x v t| ≤ 25 * B * planeTailProfile x := by
    have hs := mul_le_mul_of_nonneg_left (planeTailProfile_line_le x v ht hv) hB
    exact (hfB _).trans (by nlinarith [hs])
  have he := first_derivative_two_point_bound (scalarLine_smooth hf x v) hh hM hline
    (hb 0 (by norm_num)) (hb h (by simpa only [abs_of_pos hh] using hh1))
  have hc : h ^ 3 = planeTailProfile x := derivativeTail_cube x
  have hd : iteratedDeriv 1 (scalarLine f x v) 0 =
      iteratedFDeriv ℝ 1 f x (fun _ => v) := by
    simpa only [zero_smul, add_zero] using scalarLine_iteratedDeriv hf x v 1 0
  rw [hd] at he
  have hp : h ^ 3 ≤ h ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh1)]
  apply (mul_le_mul_iff_left₀ hh).mp
  calc
    _ ≤ 2 * (25 * B * planeTailProfile x) + M * h ^ 2 := he
    _ ≤ (50 * B + M) * h ^ 2 := by
      rw [← hc]
      nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 50 * B by positivity)]
    _ = ((50 * B + M) * derivativeTail x) * h := by dsimp [h]; ring


end ForcedComputation.VelocityDetector

end

end OAI
