import OAI.Geometry.SurfaceImmersion.Correction.InitialCorrectionStage
import OAI.Geometry.SurfaceImmersion.Geometry.InitializationPowers

namespace OAI

/-! Initial exact correction from the finite power bounds in the manuscript. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance polynomialInitialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialInitialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialInitialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialInitialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialInitialSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialInitialSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection
open ExactCorrection

/-- The first correction block for a power-controlled input family. The
geometric threshold and radii remain explicit; all finite jet and metric
smallness conditions are discharged here by the prescribed powers of `z`. -/
theorem exact_correction_from_polynomial_initial_data
    {μ N C D e : ℝ} (hμ : 1 < μ) (hN : 20*μ < N)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 < e) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/32 ∧ ∀ z : ℝ, 0 < z → z < η →
    ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F)
      (d : CorrectionGeometry g F) (c : PreparedCorrection d),
      z^μ < c.ε 0 → 1/z^4 ≤ c.budget → z^4 ≤ c.ρ → 8*e ≤ c.a →
      d.A.ShiftedBound 2 440 z (C/z^2) F →
      d.A.TensorWeightedBound 1 440 D g.inner →
      d.A.TensorWeightedBound 1 440 (C*z^N) (inducedTensor F-g.inner) →
      ∃ G : M → Space, IsSmoothIsometricImmersion M g G ∧
        d.A.WeightedBound 1 2 (z^4/8+2*c.ρ*z^μ) (G-F) := by
  obtain ⟨η,hη,hη32,hsmall⟩ := initialization_budget_threshold hμ hN hC hD he
  refine ⟨η,hη,hη32,?_⟩
  intro z hz hzη F hF d c htε hbudget hρ ha hmap hmetric herr
  obtain ⟨htz,ht32,hMB,hHB,hnear,herrB⟩ := hsmall z hz hzη
  have ht : 0 < z^μ := Real.rpow_pos_of_pos hz _
  have ht1 : z^μ ≤ 1 := by linarith
  have hP : 0 ≤ C/z^2 := div_nonneg hC (sq_nonneg z)
  have hmap0 : d.A.ShiftedBound 2 0 1 (C/z^2) F := by
    intro i j hj x
    have hj2 : j-2 = 0 := by omega
    have hh := hmap i j (by omega) x
    simpa only [hj2,pow_zero,one_mul] using hh
  have hmetric0 : d.A.TensorWeightedBound 1 0 D g.inner :=
    fun i => (hmetric i).mono_order (Nat.zero_le _)
  have hδ : ((z^μ)^(10 : ℝ))^2 = z^(20*μ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Real.rpow_nonneg hz.le _),
      ← Real.rpow_mul hz.le]
    congr 1
    norm_num
    ring
  have herr' : d.A.TensorWeightedBound (z^μ) 440
      (((z^μ)^(10 : ℝ))^2*e) (inducedTensor F-g.inner) := by
    intro i
    rw [hδ]
    exact ((herr i).shrink_scale ht.le ht1).mono_const herrB
  have hnear' : ((z^μ)^(10 : ℝ))^2*(C/z^2) ≤ c.ρ/8 := by
    rw [hδ]
    exact hnear.trans (div_le_div_of_nonneg_right hρ (by norm_num))
  obtain ⟨seed,hseed⟩ := c.initial_stage_of_scaled_bounds hF ht ht32 htε hz htz
    hP hP hD he.le hmap0 hmap hmetric0 hmetric herr'
    (hMB.trans hbudget) (hHB.trans hbudget) hnear' (by linarith)
  obtain ⟨G,hG,hclose⟩ := c.exact_correction_initial_displacement hF ht ht32 hP hmap0 seed hseed
  refine ⟨G,hG,fun i => (hclose i).mono_const ?_⟩
  rw [hδ]
  linarith

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
