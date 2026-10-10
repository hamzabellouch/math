import OAI.Geometry.EinsteinFour.JacobiSymmetricKernel
import OAI.Geometry.EinsteinFour.JacobiDeterminantJensen

namespace OAI

/-! The finite lower determinant comparison at total Weyl energy three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem finite_log_determinant_lower {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (hG : G.PosSemidef) (hGentry : ∀ i j, 0 ≤ G i j)
    (R : Fin N → Ω → NormalMatrix) (hR : ∀ i, Continuous (R i))
    (hpos : ∀ i x, (R i x).PosSemidef ∧ (R i x).trace = 3)
    (hE : ∀ i, (∫ x, ‖R i x‖ ^ 2 ∂μ) = 15 / 2)
    (hscalar : (1 - (3 : ℝ) • G).PosDef)
    (hI : ∀ x, (1 - symmetricCurvatureKernel S (fun i => R i x)).PosDef) :
    (5 / 6 : ℝ) * Real.log (1 - (3 : ℝ) • G).det - G.trace / 2 ≤
      ∫ x, Real.log (1 - curvatureKernel G (fun i => R i x)).det ∂μ := by
  let H := fun x => symmetricCurvatureKernel S (fun i => R i x)
  have hH : Continuous H :=
    (continuous_const.mul ((continuous_pi hR).matrix_blockDiagonal)).mul continuous_const
  have hp : ∀ x, (H x).PosSemidef := fun x =>
    symmetricCurvatureKernel_posSemidef S hSt _ (fun i => (hpos i x).1)
  have htr (k : ℕ) : (((3 : ℝ) • G) ^ k).trace = 3 ^ k * (G ^ k).trace := by
    rw [smul_pow, Matrix.trace_smul, smul_eq_mul]
  have hfirst : (∫ x, (H x).trace ∂μ) = ((3 : ℝ) • G).trace := by
    have he (x : Ω) : (H x).trace = 3 * G.trace :=
      symmetricCurvatureKernel_trace S G hS _ (fun i => (hpos i x).2)
    simp only [he, integral_const, probReal_univ, Matrix.trace_smul, smul_eq_mul, one_mul]
  have hmoment (k : ℕ) : (∫ x, (H x ^ (k + 2)).trace ∂μ) ≤
      (5 / 6 : ℝ) * (((3 : ℝ) • G) ^ (k + 2)).trace := by
    have he (x : Ω) : (H x ^ (k + 2)).trace =
        (curvatureKernel G (fun i => R i x) ^ (k + 2)).trace :=
      symmetricCurvatureKernel_trace_pow S G hS _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall he), htr]
    simpa only [mul_assoc] using integral_trace_curvatureKernel_power_le G hGentry R hR hpos hE k
  have h := expected_log_det_lower H ((3 : ℝ) • G) hH hp hI
    (hG.smul (by norm_num)) hscalar hfirst hmoment
  have he (x : Ω) : (1 - H x).det = (1 - curvatureKernel G (fun i => R i x)).det :=
    symmetricCurvatureKernel_det S G hS _
  simp only [Matrix.trace_smul, smul_eq_mul] at h
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => congrArg Real.log (he x)))] at h
  convert h using 1
  ring

theorem finite_determinant_lower {N : ℕ}
    (S G : Matrix (Fin N) (Fin N) ℝ) (hS : S * S = G) (hSt : Sᵀ = S)
    (hG : G.PosSemidef) (hGentry : ∀ i j, 0 ≤ G i j)
    (R : Fin N → Ω → NormalMatrix) (hR : ∀ i, Continuous (R i))
    (hpos : ∀ i x, (R i x).PosSemidef ∧ (R i x).trace = 3)
    (hE : ∀ i, (∫ x, ‖R i x‖ ^ 2 ∂μ) = 15 / 2)
    (hscalar : (1 - (3 : ℝ) • G).PosDef)
    (hI : ∀ x, (1 - symmetricCurvatureKernel S (fun i => R i x)).PosDef) :
    Real.exp ((5 / 6 : ℝ) * Real.log (1 - (3 : ℝ) • G).det - G.trace / 2) ≤
      ∫ x, (1 - curvatureKernel G (fun i => R i x)).det ∂μ := by
  have hf : Continuous (fun x => (1 - curvatureKernel G (fun i => R i x)).det) :=
    (continuous_const.sub (continuous_const.mul
      ((continuous_pi hR).matrix_blockDiagonal))).matrix_det
  have hp (x : Ω) : 0 < (1 - curvatureKernel G (fun i => R i x)).det := by
    rw [← symmetricCurvatureKernel_det S G hS]
    exact (hI x).det_pos
  exact (Real.exp_le_exp.mpr
    (finite_log_determinant_lower S G hS hSt hG hGentry R hR hpos hE hscalar hI)).trans
      (exp_integral_log_le_integral _ hf hp)

end
end PositiveEinsteinFour.Jacobi

end OAI
