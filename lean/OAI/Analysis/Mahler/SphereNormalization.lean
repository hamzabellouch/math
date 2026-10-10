import OAI.Analysis.Mahler.SphereForms
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace OAI

open MeasureTheory Metric
open scoped BigOperators
namespace Mahler

lemma complexEuclidean_finrank_real (n : ℕ) :
    Module.finrank ℝ (ComplexEuclidean n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexEuclidean n)]
  simp [ComplexEuclidean, Complex.finrank_real_complex]

/-- The concrete area measure induced by Euclidean volume on the unit sphere. -/
noncomputable def sphereArea (n : ℕ) : Measure (sphere (0 : ComplexEuclidean n) 1) :=
  (volume : Measure (ComplexEuclidean n)).toSphere

/-- The numerical integral for sphere normalization. This does not
assume equality of the constant density and the reference exterior form. -/
theorem reference_sphere_density_integral (n : ℕ) (hn : 1 ≤ n) :
    (∫ _z : sphere (0 : ComplexEuclidean n) 1,
      ((n - 1).factorial : ℝ) / 2 ∂sphereArea n) = Real.pi ^ n := by
  have hdim := complexEuclidean_finrank_real n
  have : Nontrivial (ComplexEuclidean n) :=
    Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  have hv : (volume : Measure (ComplexEuclidean n)).real (ball 0 1) =
      Real.pi ^ n / (n.factorial : ℝ) := by
    rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even hdim]
    simp
    positivity
  rw [integral_const, sphereArea, Measure.toSphere_real_apply_univ, hdim, hv, smul_eq_mul]
  have hn' : n = (n - 1) + 1 := by omega
  have hfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
    conv_lhs => rw [hn', Nat.factorial_succ]
    push_cast
    congr 1
    exact_mod_cast hn'.symm
  rw [hfac]
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hfn : ((n - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - 1)
  push_cast
  field_simp

end Mahler

end OAI
