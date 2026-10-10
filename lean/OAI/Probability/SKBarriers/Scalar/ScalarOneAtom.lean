import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSpinRecursion

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def scalarMagnetization (z : ℝ) : ℝ := Real.sinh z/Real.cosh z

theorem scalarMagnetization_zero : scalarMagnetization 0 = 0 := by
  simp [scalarMagnetization]

theorem scalarMagnetization_hasDerivAt (z : ℝ) :
    HasDerivAt scalarMagnetization (1/(Real.cosh z)^2) z := by
  have H : HasDerivAt scalarMagnetization
      ((Real.cosh z*Real.cosh z-Real.sinh z*Real.sinh z)/(Real.cosh z)^2) z :=
    (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z) (Real.cosh_pos z).ne'
  apply H.congr_deriv
  congr 1
  nlinarith [Real.cosh_sq_sub_sinh_sq z]

theorem scalarMagnetization_derivative_identity (z : ℝ) :
    1/(Real.cosh z)^2 = 1-(scalarMagnetization z)^2 := by
  have H := Real.cosh_sq_sub_sinh_sq z
  unfold scalarMagnetization
  field_simp
  nlinarith

theorem scalarMagnetization_sq_le_one (z : ℝ) : (scalarMagnetization z)^2 ≤ 1 := by
  have H := scalarMagnetization_derivative_identity z
  have := div_nonneg (by norm_num : (0:ℝ) ≤ 1) (sq_nonneg (Real.cosh z))
  linarith

theorem scalarMagnetization_abs_le_one (z : ℝ) : |scalarMagnetization z| ≤ 1 :=
  (sq_le_one_iff_abs_le_one _).mp (scalarMagnetization_sq_le_one z)

theorem scalarMagnetization_lipschitz : LipschitzWith 1 scalarMagnetization := by
  rw [← lipschitzOnWith_univ]
  apply (convex_univ : Convex ℝ (Set.univ : Set ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z _ => (scalarMagnetization_hasDerivAt z).hasDerivWithinAt)
  intro z _
  change ‖(1/(Real.cosh z)^2:ℝ)‖ ≤ (1:ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity)).mpr
  nlinarith [Real.one_le_cosh z]

theorem scalarMagnetization_abs_le (z : ℝ) : |scalarMagnetization z| ≤ |z| := by
  simpa [scalarMagnetization_zero,Real.dist_eq] using scalarMagnetization_lipschitz.dist_le_mul z 0

theorem scalarSpinTerminal_hasDerivAt (z : ℝ) :
    HasDerivAt scalarSpinTerminal (scalarMagnetization z) z := by
  have H := ((Real.hasDerivAt_cosh z).const_mul 2).log
    (mul_pos (by norm_num : (0:ℝ)<2) (Real.cosh_pos z)).ne'
  apply H.congr_deriv
  dsimp [scalarMagnetization]
  field_simp

theorem scalarSpinTerminal_lipschitz : LipschitzWith 1 scalarSpinTerminal := by
  rw [← lipschitzOnWith_univ]
  apply (convex_univ : Convex ℝ (Set.univ : Set ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z _ => (scalarSpinTerminal_hasDerivAt z).hasDerivWithinAt)
  intro z _
  change ‖scalarMagnetization z‖ ≤ (1:ℝ)
  simpa only [Real.norm_eq_abs] using scalarMagnetization_abs_le_one z

theorem scalarSpinTerminal_integrable (v : ℝ) :
    Integrable (fun y => scalarSpinTerminal (v*y)) (gaussianReal 0 1) := by
  have hi : Integrable (fun y : ℝ => |scalarSpinTerminal 0|+|v| * |y|) (gaussianReal 0 1) :=
    (integrable_const _).add (((memLp_id_gaussianReal 1).integrable (by norm_num)).norm.const_mul |v|)
  apply hi.mono' (scalarSpinTerminal_lipschitz.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  filter_upwards [] with y
  have H := scalarSpinTerminal_lipschitz.dist_le_mul (v*y) 0
  simp only [Real.dist_eq,sub_zero,NNReal.coe_one,one_mul,abs_mul] at H
  rw [Real.norm_eq_abs]
  have h := abs_add_le (scalarSpinTerminal (v*y)-scalarSpinTerminal 0) (scalarSpinTerminal 0)
  rw [sub_add_cancel] at h
  change |scalarSpinTerminal (v*y)| ≤ |scalarSpinTerminal 0|+|v| * |y|
  linarith

def scalarGaussianValue (v : ℝ) : ℝ := ∫ y, scalarSpinTerminal (v*y) ∂gaussianReal 0 1

theorem scalarGaussianValue_hasDerivAt (v : ℝ) :
    HasDerivAt scalarGaussianValue (∫ y, y*scalarMagnetization (v*y) ∂gaussianReal 0 1) v := by
  have HC := scalarMagnetization_lipschitz.continuous
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) (bound := fun y : ℝ => |y|)
    (F := fun x y : ℝ => scalarSpinTerminal (x*y))
    (F' := fun x y : ℝ => y*scalarMagnetization (x*y))
    (by simp) (Filter.Eventually.of_forall (fun _ =>
      (scalarSpinTerminal_lipschitz.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable))
    (scalarSpinTerminal_integrable v)
    (continuous_id.mul (HC.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y _ _ => ?_))
    ((memLp_id_gaussianReal 1).integrable (by norm_num)).norm
    (Filter.Eventually.of_forall (fun y x _ => ?_))).2
  · rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (scalarMagnetization_abs_le_one _)
  · simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using (scalarSpinTerminal_hasDerivAt (x*y)).comp x ((hasDerivAt_id x).mul_const y)
end SK.Analytic

end
end

end

end OAI
