import OAI.Geometry.IsometricImmersion.Metric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section
open scoped Matrix BigOperators
open Set Metric

namespace SmoothLocal.Geometry

abbrev PlanarAxis := EuclideanSpace ℝ (Fin 2)

def axisRotation (a : PlanarAxis) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![a 1, a 0], ![-a 0, a 1]]

theorem axisRotation_yaxis (a : PlanarAxis) :
    axisRotation a *ᵥ Pi.single 1 (1 : ℝ) = WithLp.ofLp a := by
  rw [Matrix.mulVec_single_one]
  funext i
  fin_cases i <;> rfl

theorem planarAxis_sq_sum {a : PlanarAxis} (ha : ‖a‖ = 1) : a 0 ^ 2 + a 1 ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq a
  rw [ha, one_pow, Fin.sum_univ_two] at h
  exact h.symm

theorem axisRotation_transpose_mul {a : PlanarAxis} (ha : ‖a‖ = 1) :
    (axisRotation a)ᵀ * axisRotation a = 1 := by
  have hs := planarAxis_sq_sum ha
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [axisRotation] <;> nlinarith [hs]

theorem axisRotation_mul_transpose {a : PlanarAxis} (ha : ‖a‖ = 1) :
    axisRotation a * (axisRotation a)ᵀ = 1 := by
  have hs := planarAxis_sq_sum ha
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [axisRotation] <;> nlinarith [hs]

theorem axisRotation_det {a : PlanarAxis} (ha : ‖a‖ = 1) : (axisRotation a).det = 1 := by
  have hs := planarAxis_sq_sum ha
  rw [Matrix.det_fin_two]
  simp [axisRotation]
  nlinarith [hs]

theorem exists_finite_unit_axis_net :
    ∃ axes : Finset PlanarAxis, (∀ a ∈ axes, ‖a‖ = 1) ∧
      ∀ v : PlanarAxis, ‖v‖ = 1 → ∃ a ∈ axes, dist v a < (1 / 1000 : ℝ) := by
  classical
  obtain ⟨s, hsphere, hsfinite, hcover⟩ :=
    (isCompact_sphere (0 : PlanarAxis) 1).finite_cover_balls
      (show (0 : ℝ) < 1 / 1000 by norm_num)
  refine ⟨hsfinite.toFinset, ?_, ?_⟩
  · intro a ha
    have hmem := hsphere (hsfinite.mem_toFinset.mp ha)
    simpa only [Metric.mem_sphere, dist_zero_right] using hmem
  · intro v hv
    have hvs : v ∈ sphere (0 : PlanarAxis) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hv
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcover hvs)
    obtain ⟨has, hva⟩ := Set.mem_iUnion.mp ha
    exact ⟨a, hsfinite.mem_toFinset.mpr has, hva⟩

def orientationAxes : Finset PlanarAxis := Classical.choose exists_finite_unit_axis_net

theorem orientationAxes_unit (a : PlanarAxis) (ha : a ∈ orientationAxes) : ‖a‖ = 1 :=
  (Classical.choose_spec exists_finite_unit_axis_net).1 a ha

theorem orientationAxes_cover (v : PlanarAxis) (hv : ‖v‖ = 1) :
    ∃ a ∈ orientationAxes, dist v a < (1 / 1000 : ℝ) :=
  (Classical.choose_spec exists_finite_unit_axis_net).2 v hv

def orientationRotations : Finset (Matrix (Fin 2) (Fin 2) ℝ) := by
  classical
  exact orientationAxes.image axisRotation

theorem orientationRotations_properties {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : R ∈ orientationRotations) : Rᵀ * R = 1 ∧ R * Rᵀ = 1 ∧ R.det = 1 := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hR
  exact ⟨axisRotation_transpose_mul (orientationAxes_unit a ha),
    axisRotation_mul_transpose (orientationAxes_unit a ha),
    axisRotation_det (orientationAxes_unit a ha)⟩

theorem orientationRotations_cover (v : PlanarAxis) (hv : ‖v‖ = 1) :
    ∃ R ∈ orientationRotations,
      dist v (WithLp.toLp 2 (R *ᵥ Pi.single 1 (1 : ℝ))) < (1 / 1000 : ℝ) := by
  classical
  obtain ⟨a, ha, hva⟩ := orientationAxes_cover v hv
  refine ⟨axisRotation a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
  simpa only [axisRotation_yaxis, WithLp.toLp_ofLp] using hva

end SmoothLocal.Geometry

end

end OAI
