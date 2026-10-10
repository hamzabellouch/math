import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedCoulombMass
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! The inverse-fifth-power tail is integrable in three dimensions, with the
exact inverse-square dependence needed when summing far-cell errors. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def inverseFifthRadial (r : ℝ) : ℝ → ℝ :=
  (Set.Ioi r).indicator (fun t => t^(-5:ℝ))

def inverseFifthTail (r : ℝ) (x : Position) : ℝ := inverseFifthRadial r ‖x‖

private theorem inverseFifthRadial_weight {r : ℝ} (hr : 0 < r) (t : ℝ) :
    t^2*inverseFifthRadial r t = (Set.Ioi r).indicator (fun t => t^(-3:ℝ)) t := by
  by_cases ht : r < t
  · simp only [inverseFifthRadial,Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]
    have hp : 0 < t := hr.trans ht
    rw [show (-3:ℝ) = 2+(-5) by norm_num,Real.rpow_add hp,Real.rpow_two]
  · simp [inverseFifthRadial,ht]

private theorem inverseFifthRadial_weight_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t^2*inverseFifthRadial r t) (Set.Ioi 0) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hr
  have h := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  simpa only [inverseFifthRadial_weight hr] using h.integrableOn

private theorem inverseFifthRadial_weight_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in Set.Ioi (0:ℝ), t^2*inverseFifthRadial r t) = 1/(2*r^2) := by
  simp_rw [inverseFifthRadial_weight hr]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi,max_eq_left hr.le]
  have hi := integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hr
  convert hi using 1
  norm_num [Real.rpow_neg,Real.rpow_two]
  ring

theorem inverseFifthTail_integrable {r : ℝ} (hr : 0 < r) : Integrable (inverseFifthTail r) := by
  apply (integrable_fun_norm_addHaar (E := Position) volume (f := inverseFifthRadial r)).mpr
  simpa only [finrank_euclideanSpace_fin,Nat.reduceSub,smul_eq_mul] using
    inverseFifthRadial_weight_integrable hr

theorem inverseFifthTail_integral {r : ℝ} (hr : 0 < r) :
    (∫ x : Position, inverseFifthTail r x) = 2*Real.pi/r^2 := by
  change (∫ x : Position, inverseFifthRadial r ‖x‖) = _
  rw [integral_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace_fin,Nat.reduceSub,smul_eq_mul]
  rw [inverseFifthRadial_weight_integral hr]
  simp only [Measure.real,EuclideanSpace.volume_ball_fin_three,ENNReal.ofReal_one,one_pow,
    one_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3),nsmul_eq_mul]
  norm_num [Position,finrank_euclideanSpace_fin]
  ring

theorem inverseFifthTail_of_gt {r : ℝ} (x : Position) (hx : r < ‖x‖) :
    inverseFifthTail r x = ‖x‖^(-5:ℝ) := by
  unfold inverseFifthTail inverseFifthRadial
  exact Set.indicator_of_mem (Set.mem_Ioi.mpr hx) _

theorem inverseFifthTail_nonneg (r : ℝ) (x : Position) : 0 ≤ inverseFifthTail r x := by
  by_cases hx : r < ‖x‖
  · rw [inverseFifthTail_of_gt x hx]
    exact Real.rpow_nonneg (norm_nonneg x) _
  · simp [inverseFifthTail,inverseFifthRadial,hx]

theorem inverseFifthTail_eq_inv_pow {r : ℝ} (x : Position) (hx : r < ‖x‖) :
    inverseFifthTail r x = 1/‖x‖^5 := by
  rw [inverseFifthTail_of_gt x hx]
  simp

theorem inverseFifthTail_measurable (r : ℝ) : Measurable (inverseFifthTail r) := by
  have he : inverseFifthTail r = {x : Position | r < ‖x‖}.indicator (fun x => 1/‖x‖^5) := by
    funext x
    by_cases hx : r < ‖x‖
    · rw [inverseFifthTail_eq_inv_pow x hx,
        Set.indicator_of_mem (show x ∈ {x : Position | r < ‖x‖} from hx)]
    · simp [inverseFifthTail,inverseFifthRadial,hx]
  rw [he]
  exact (measurable_const.div (continuous_norm.measurable.pow_const 5)).indicator
    (isOpen_lt continuous_const continuous_norm).measurableSet

theorem inverseFifthTail_le {r : ℝ} (hr : 0 < r) (x : Position) :
    inverseFifthTail r x ≤ 1/r^5 := by
  by_cases hx : r < ‖x‖
  · rw [inverseFifthTail_eq_inv_pow x hx]
    exact one_div_le_one_div_of_le (pow_pos hr 5) (pow_le_pow_left₀ hr.le hx.le 5)
  · have he : inverseFifthTail r x = 0 := by simp [inverseFifthTail,inverseFifthRadial,hx]
    rw [he]
    positivity

theorem translatedInverseFifth_integrable (y : Position) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => inverseFifthTail r (y-x)) :=
  (volume.measurePreserving_sub_left y).integrable_comp_of_integrable
    (inverseFifthTail_integrable hr)

theorem translatedInverseFifth_integral (y : Position) {r : ℝ} (hr : 0 < r) :
    (∫ x, inverseFifthTail r (y-x)) = 2*Real.pi/r^2 := by
  rw [integral_sub_left_eq_self,inverseFifthTail_integral hr]

end ContinuumCoulomb

end

end OAI
