import OAI.Geometry.EinsteinFour.GeodesicAverage
import OAI.Geometry.EinsteinFour.JacobiRadialDeficit

namespace OAI

/-! Specialization of mean-square geodesic averaging to actual normal
curvature matrices, using their Frobenius norm. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

local instance : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ NormalMatrix := Matrix.frobeniusNormedSpace

private instance matrixContinuousENorm : ContinuousENorm NormalMatrix :=
  @SeminormedAddGroup.toContinuousENorm NormalMatrix
    (inferInstanceAs (SeminormedAddGroup NormalMatrix))

/-- Entry coordinates preserve the Frobenius norm exactly. -/
def matrixVector : NormalMatrix →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3 × Fin 3) where
  toLinearMap :=
    { toFun := fun A => WithLp.toLp 2 (fun ij => A ij.1 ij.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' A := by
    change ‖(WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 => A ij.1 ij.2) :
      EuclideanSpace ℝ (Fin 3 × Fin 3))‖ = ‖A‖
    simp only [EuclideanSpace.norm_eq, Fintype.sum_prod_type,
      Matrix.frobenius_norm_def, Real.rpow_two, Real.sqrt_eq_rpow]

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

local instance : NormedAddCommGroup C(Ω, NormalMatrix) :=
  ContinuousMap.instNormedAddCommGroup

local instance : NormedSpace ℝ C(Ω, NormalMatrix) := ContinuousMap.normedSpace

/-- The matrix form of the averaging theorem used by the radial comparison.
The derivative is a derivative of the continuous curvature field, so its
energy is measured over all initial geodesics. -/
theorem matrix_geodesic_mean_square_lower {F G : ℝ → C(Ω, NormalMatrix)} {q t : ℝ}
    (hq : 0 ≤ q)
    (hderiv : ∀ r, HasDerivAt F (G r) r)
    (hstationary : ∀ r, (∫ x, ‖F r x‖ ^ 2 ∂μ) = q)
    (henergy : ∀ r, (∫ x, ‖G r x‖ ^ 2 ∂μ) ≤ (3 / 2) * q) :
    q * (1 - (t / Real.pi) ^ 2 / 2) ≤
      ∫ x, ‖∫ u, F (t * u) x ∂Averages.sineMeasure‖ ^ 2 ∂μ := by
  let T := matrixVector.toContinuousLinearMap.compLeftContinuous ℝ Ω
  have hd (r : ℝ) : HasDerivAt (fun r => T (F r)) (T (G r)) r :=
    T.hasFDerivAt.comp_hasDerivAt r (hderiv r)
  have hs (r : ℝ) : (∫ x, ‖T (F r) x‖ ^ 2 ∂μ) = q := by
    change (∫ x, ‖matrixVector (F r x)‖ ^ 2 ∂μ) = q
    simpa only [matrixVector.norm_map] using hstationary r
  have he (r : ℝ) : (∫ x, ‖T (G r) x‖ ^ 2 ∂μ) ≤ (3 / 2) * q := by
    change (∫ x, ‖matrixVector (G r x)‖ ^ 2 ∂μ) ≤ (3 / 2) * q
    simpa only [matrixVector.norm_map] using henergy r
  have h := Averages.geodesic_mean_square_lower hq hd hs he (t := t)
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun r =>
    HasDerivAt.continuousAt (F := C(Ω, NormalMatrix)) (hderiv r)
  have hc : Continuous (fun u => F (t * u)) :=
    hF.comp (continuous_const.mul continuous_id)
  have hi (x : Ω) : Integrable (fun u => F (t * u) x) Averages.sineMeasure :=
    Averages.integrable_sineMeasure ((ContinuousMap.evalCLM ℝ x).continuous.comp hc)
  have hn (x : Ω) :
      ‖∫ u, T (F (t * u)) x ∂Averages.sineMeasure‖ =
      ‖∫ u, F (t * u) x ∂Averages.sineMeasure‖ := by
    change ‖∫ u, matrixVector.toContinuousLinearMap (F (t * u) x)
      ∂Averages.sineMeasure‖ = _
    rw [matrixVector.toContinuousLinearMap.integral_comp_comm (hi x)]
    exact matrixVector.norm_map _
  simpa only [hn] using h

end

end PositiveEinsteinFour.Jacobi

end OAI
