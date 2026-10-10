import OAI.Geometry.RCD.Coordinates.ProjectionMeasuredCoordinates
import OAI.Geometry.RCD.Coordinates.LocalCoordinateExtension

namespace OAI

/-! # Measured projection coordinates from local harmonic representatives -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
/-- A measurable extension retains the same local harmonic representative. -/
theorem FirstOrderSplittingOn.measurable_values {μ : Measure X}
    {hQ : QuadraticCheegerEnergy μ} {n : ℕ} {q : X} {r epsilon : ℝ}
    {u : Fin n → SobolevSpace μ hQ} {V : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ q r epsilon u V) :
    ∃ W : X → Euclidean n, Measurable W ∧ EqOn V W (ball q r) ∧
      FirstOrderSplittingOn μ hQ q r epsilon u W := by
  obtain ⟨W, hW, hEq⟩ := exists_measurable_local_extension measurableSet_ball h.continuous
  refine ⟨W, hW, hEq, { h with representative := ?_, continuous := ?_ }⟩
  · intro j
    filter_upwards [h.representative j, ae_restrict_mem measurableSet_ball] with x hx hxs
    exact hx.trans (congrArg (fun z : Euclidean n => z j) (hEq hxs))
  · exact h.continuous.congr (fun x hx => (hEq hx).symm)

omit [ProperSpace X] in
/-- The local harmonic coordinates admit a measurable representative with
exactly the same metric data and the required measured approximation. -/
theorem projection_measured_local_coordinates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hmeasured : LocalMeasuredCoordinateInput hX) {error : ℝ} (herror : 0 < error) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {q : X} {s epsilon : ℝ}, 0 < s →
      -delta / 32 ≤ K * s ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (V : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic q (2 * s) epsilon u V →
      V q = 0 →
      IsPointedApproximation q 0 (s / 64) 4 delta (fun x => (s / 64)⁻¹ • V x) →
      ∃ W : X → Euclidean n, Measurable W ∧ EqOn V W (ball q (2 * s)) ∧
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic q (2 * s) epsilon u W ∧
        W q = 0 ∧
        IsPointedApproximation q 0 (s / 64) 4 delta (fun x => (s / 64)⁻¹ • W x) ∧
        IsMeasuredEuclideanApproximation (hausdorff n X) n q s (1 / 1024) error
          (fun x => s⁻¹ • W x) := by
  obtain ⟨delta, hdelta, happly⟩ := projection_measured_coordinates hX hn hmeasured herror
  refine ⟨delta, hdelta, ?_⟩
  intro q s epsilon hs hcurv u V hfirst hcenter hmetric
  obtain ⟨W, hW, hEq, hfirstW⟩ := hfirst.measurable_values
  have hcenterW : W q = 0 := (hEq (mem_ball_self (by positivity))).symm.trans hcenter
  have hmetricW : IsPointedApproximation q 0 (s / 64) 4 delta
      (fun x => (s / 64)⁻¹ • W x) := by
    apply hmetric.congr_on_ball (by positivity)
    intro x hx
    have hxs : x ∈ ball q (2 * s) := by
      have hdist := mem_closedBall.mp hx
      exact mem_ball.mpr (by linarith)
    dsimp only
    rw [hEq hxs]
  have hresult := happly q s hs hcurv (fun x => (s / 64)⁻¹ • W x)
    ((continuous_const_smul ((s / 64)⁻¹)).measurable.comp hW)
    (by rw [hcenterW, smul_zero]) hmetricW
  have hfactor : (1 / 64 : ℝ) * (s / 64)⁻¹ = s⁻¹ := by field_simp
  refine ⟨W, hW, hEq, hfirstW, hcenterW, hmetricW, ?_⟩
  simpa only [smul_smul, hfactor] using hresult

end RegularPointCoordinates

end

end OAI
