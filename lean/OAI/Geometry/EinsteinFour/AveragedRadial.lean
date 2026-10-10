import OAI.Geometry.EinsteinFour.MatrixGeodesicAverage

namespace OAI

/-! Averaging the proved Jacobi determinant deficit over initial geodesics.
The density is explicitly truncated at the first conjugate point. -/

namespace PositiveEinsteinFour.Jacobi

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

local instance : NormedAddCommGroup NormalMatrix := Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ NormalMatrix := Matrix.frobeniusNormedSpace

private instance matrixContinuousENorm : ContinuousENorm NormalMatrix :=
  @SeminormedAddGroup.toContinuousENorm NormalMatrix
    (inferInstanceAs (SeminormedAddGroup NormalMatrix))

/-- The radial Jacobian, set to zero once a conjugate point has occurred. -/
def RegularJacobi.truncatedDensity {t : ℝ} (d : RegularJacobi t) : ℝ := by
  classical
  exact if ∀ s, 0 < s → s ≤ t → IsUnit (d.J s) then (d.J t).det else 0

theorem RegularJacobi.truncatedDensity_le {t : ℝ} (d : RegularJacobi t)
    (ht : 0 < t) (htπ : t < Real.pi)
    (hR : Continuous d.R) (hpos : ∀ s, (d.R s).PosSemidef)
    (htrace : ∀ s, (d.R s).trace = 3)
    {L : ℝ} (hL : 0 ≤ L)
    (hc : Continuous (fun s => Averages.sineWeight s • radialCurvature d.R t s))
    (hLip : ∀ s r,
      ‖Averages.sineWeight s • radialCurvature d.R t s -
        Averages.sineWeight r • radialCurvature d.R t r‖ ≤ L * |s - r|) :
    d.truncatedDensity ≤ Real.sin t ^ 3 *
      (1 - lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6 *
        ‖∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature d.R t s‖ ^ 2) := by
  classical
  unfold truncatedDensity
  split_ifs with hpre
  · exact d.radial_determinant_deficit ht htπ hpre hR hpos htrace hL hc hLip
  · exact d.radial_deficit_nonneg ht.le htπ hR hpos htrace

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

local instance : NormedAddCommGroup C(Ω, NormalMatrix) :=
  ContinuousMap.instNormedAddCommGroup

local instance : NormedSpace ℝ C(Ω, NormalMatrix) := ContinuousMap.normedSpace

/-- The actual averaged radial determinant estimate. Its mean-square and
energy hypotheses apply to the field, rather than to individual geodesics.
All matrix comparison, finite approximation and averaging steps are proved. -/
theorem averaged_truncatedDensity_le {t q : ℝ}
    (d : Ω → RegularJacobi t) {F G : ℝ → C(Ω, NormalMatrix)}
    (ht : 0 < t) (htπ : t < Real.pi) (hq : 0 ≤ q)
    (hderiv : ∀ r, HasDerivAt F (G r) r)
    (hstationary : ∀ r, (∫ x, ‖F r x‖ ^ 2 ∂μ) = q)
    (henergy : ∀ r, (∫ x, ‖G r x‖ ^ 2 ∂μ) ≤ (3 / 2) * q)
    (hcurvature : ∀ x r, (d x).R r = 1 + F r x)
    (hpos : ∀ x r, ((d x).R r).PosSemidef)
    (htrace : ∀ x r, ((d x).R r).trace = 3)
    (hLip : ∀ x, ∃ L : ℝ, 0 ≤ L ∧ ∀ s r,
      ‖Averages.sineWeight s • radialCurvature (d x).R t s -
        Averages.sineWeight r • radialCurvature (d x).R t r‖ ≤ L * |s - r|)
    (hD : Integrable (fun x => (d x).truncatedDensity) μ) :
    (∫ x, (d x).truncatedDensity ∂μ) ≤ Real.sin t ^ 3 *
      (1 - lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6 *
        q * (1 - (t / Real.pi) ^ 2 / 2)) := by
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun r => (hderiv r).continuousAt
  have hFt : Continuous (fun u => F (t * u)) := hF.comp (continuous_const.mul continuous_id)
  let B : C(Ω, NormalMatrix) := ∫ u, F (t * u) ∂Averages.sineMeasure
  have hB (x : Ω) : B x = ∫ u, F (t * u) x ∂Averages.sineMeasure :=
    ContinuousMap.integral_apply (Averages.integrable_sineMeasure hFt) x
  have hR (x : Ω) : Continuous (d x).R := by
    have hc := (ContinuousMap.evalCLM ℝ x).continuous.comp hF
    have heq : (d x).R = fun r => 1 + F r x := funext (hcurvature x)
    rw [heq]
    exact continuous_const.add hc
  have hA (x : Ω) : Continuous (fun s =>
      Averages.sineWeight s • radialCurvature (d x).R t s) := by
    unfold Averages.sineWeight radialCurvature
    fun_prop
  have hmean (x : Ω) :
      (∫ s in (0 : ℝ)..1, Averages.sineWeight s • radialCurvature (d x).R t s) = B x := by
    rw [← Averages.integral_sineMeasure, hB]
    congr 1
    funext s
    simp [radialCurvature, hcurvature, mul_comm]
  have hQ : Integrable (fun x => ‖B x‖ ^ 2) μ := by
    rw [← integrableOn_univ]
    exact (B.continuous.norm.pow 2).continuousOn.integrableOn_compact isCompact_univ
  let c := lossFactor (t ^ 2 / (Real.pi ^ 2 - t ^ 2)) / 6
  have hc : 0 ≤ c := by dsimp [c, lossFactor]; positivity
  have hi : Integrable (fun x => Real.sin t ^ 3 * (1 - c * ‖B x‖ ^ 2)) μ :=
    ((integrable_const 1).sub (hQ.const_mul c)).const_mul _
  have hpoint (x : Ω) : (d x).truncatedDensity ≤
      Real.sin t ^ 3 * (1 - c * ‖B x‖ ^ 2) := by
    obtain ⟨L, hL, hbound⟩ := hLip x
    simpa only [hmean, c] using (d x).truncatedDensity_le ht htπ (hR x)
      (hpos x) (htrace x) hL (hA x) hbound
  have hint := integral_mono hD hi hpoint
  have heq : (∫ x, Real.sin t ^ 3 * (1 - c * ‖B x‖ ^ 2) ∂μ) =
      Real.sin t ^ 3 * (1 - c * (∫ x, ‖B x‖ ^ 2 ∂μ)) := by
    rw [integral_const_mul, integral_sub (integrable_const 1) (hQ.const_mul c),
      integral_const_mul]
    simp
  rw [heq] at hint
  have hmeanbound := matrix_geodesic_mean_square_lower hq hderiv hstationary henergy (t := t)
  simp_rw [← hB] at hmeanbound
  have hmul := mul_le_mul_of_nonneg_left hmeanbound hc
  have hsin : 0 ≤ Real.sin t ^ 3 := pow_nonneg (Real.sin_pos_of_pos_of_lt_pi ht htπ).le 3
  have hmul' := mul_le_mul_of_nonneg_left hmul hsin
  dsimp only [c] at hint hmul'
  nlinarith only [hint, hmul']

end

end PositiveEinsteinFour.Jacobi

end OAI
