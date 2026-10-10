import OAI.Geometry.SurfaceImmersion.Geometry.UniformRadiusInputStep
import OAI.Geometry.SurfaceImmersion.Correction.CorrectionBudgetThresholds
import OAI.Geometry.SurfaceImmersion.Correction.ExplicitCorrectionBudgetThreshold
import OAI.Geometry.SurfaceImmersion.Geometry.InputSize
import OAI.Geometry.SurfaceImmersion.Correction.CorrectionGeometry

namespace OAI

/-! Fixed geometry and numerical budgets for the adaptive iteration. All the
fields below are constructed from the proved small-increment theorem. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance preparedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance preparedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance preparedDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance preparedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance preparedSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance preparedSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

/-- Construction starts at order ten, as required by the scale estimates. -/
def correctionOrder (k : ℕ) : ℕ := k+10

def correctionInputOrder (k : ℕ) : ℕ := 40*(correctionOrder k+1)

variable {g : SmoothMetric M} {F : M → Space}

/-- Uniform geometric radii and the order-dependent estimates used by the
iteration. This package is obtained by `preparedCorrection_nonempty`. -/
structure PreparedCorrection (d : CorrectionGeometry g F) where
  a : ℝ
  ρ : ℝ
  baseline : ℝ
  budget : ℝ
  a_pos : 0 < a
  ρ_pos : 0 < ρ
  baseline_nonneg : 0 ≤ baseline
  budget_pos : 0 < budget
  baseline_lt : baseline < budget/4
  ε : ℕ → ℝ
  L : ℕ → ℝ
  N : ℕ → ℕ → ℝ
  ε_pos : ∀ k, 0 < ε k
  ε_le_one : ∀ k, ε k ≤ 1
  L_nonneg : ∀ k, 0 ≤ L k
  N_nonneg : ∀ k m, 0 ≤ N k m
  preserve : ∀ k t, 0 < t → t < ε k →
    baseline+N k (correctionInputOrder k)*t^(1/5 : ℝ)*(1+budget) ≤ budget ∧
    L k*(1+2*budget)*t^(1/5 : ℝ) ≤ a/8
  step : ∀ k (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
    ∀ t : ℝ, 0 < t → t < ε k → ∀ j : ℕ,
    correctionOrder k ≤ j → j ≤ correctionOrder k+1 →
    d.A.InputBound t (correctionInputOrder k) budget G
      (normalizedTensorDefect g.inner (t^(correctionOrder k : ℝ)) G) →
    d.A.WeightedBound 1 2 (ρ/4) (G-F) →
    (∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner
      (t^(correctionOrder k : ℝ)) G) x-d.A.tensorEncode g.inner x‖ ≤ a/8) →
    ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
      (∀ m ≤ correctionOrder k/2, d.A.WeightedBound 1 m (ρ*t) U) ∧
      d.A.TensorWeightedBound (t^(6/5 : ℝ)) 0
        (L k*(1+2*budget)*t^(1/5 : ℝ))
        (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)-g.inner) ∧
      ∀ m C, 0 ≤ C → d.A.InputBound t m C G
        (normalizedTensorDefect g.inner (t^(correctionOrder k : ℝ)) G) →
        d.A.InputBound (t^(6/5 : ℝ)) m
          (baseline+N k m*t^(1/5 : ℝ)*(1+C)) (G+U)
          (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U))

namespace MetricGoodPhaseData

/-- No new analytic input is assumed in preparing the iteration. The fixed
input budget exceeds four times the baseline, and each order's threshold
preserves both the input and metric neighborhoods. -/
theorem preparedCorrection_large (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (R : ℝ) :
    ∃ c : PreparedCorrection d.toCorrectionGeometry, R < c.budget/4 := by
  classical
  obtain ⟨a,ρ,A₀,ha,hρ,hA,hall⟩ := d.uniform_radius_input_step hF
  let B₀ : ℝ := 4*(A₀+max R 0+1)
  have hR0 := le_max_right R 0
  have hRR := le_max_left R 0
  have hB₀ : 0 < B₀ := by dsimp [B₀]; linarith
  have hAB : A₀ < B₀/4 := by dsimp [B₀]; linarith
  have hAB' : A₀ < B₀ := by linarith
  have hk (k : ℕ) : 10 ≤ correctionOrder k := by unfold correctionOrder; omega
  choose ε B L N hε hε1 hB hL hN hstep using fun k => hall (correctionOrder k) (hk k) B₀ hB₀.le
  let η := fun k => ExactCorrection.correctionBudgetThreshold A₀ B₀ a
    (N k (correctionInputOrder k)) (L k 0)
  have hbudget (k : ℕ) := ExactCorrection.correctionBudgetThreshold_spec
    (N := N k (correctionInputOrder k)) (L := L k 0) hAB' ha
  have hη (k : ℕ) : 0 < η k := (hbudget k).1
  have hpres (k : ℕ) := (hbudget k).2.2
  refine ⟨⟨a,ρ,A₀,B₀,ha,hρ,hA,hB₀,hAB,
    (fun k => min (ε k) (η k)),(fun k => L k 0),N,
    (fun k => lt_min (hε k) (hη k)),
    (fun k => (min_le_left _ _).trans (hε1 k)),
    (fun k => hL k 0),hN,
    (fun k t ht htε => hpres k t ht (htε.trans_le (min_le_right _ _))),?_⟩,?_⟩
  · intro k G hG t ht htε j hj hj' hin hnear hmetric
    obtain ⟨U,hU,_,hsmall,herror,hnext⟩ := hstep k G hG t ht
      (htε.trans_le (min_le_left _ _)) j hj hj' hin hnear hmetric
    refine ⟨U,hU,hsmall,?_,hnext⟩
    have hi0 := d.A.inputBound_mono_order hin (show 0 ≤ correctionInputOrder k from Nat.zero_le _)
    simpa only [MetricGoodPhaseData.toCorrectionGeometry, show 1+B₀+B₀ = 1+2*B₀ by ring] using herror 0 B₀ hB₀.le hi0
  · change R < B₀/4
    dsimp [B₀]
    linarith

/-- The basic preparation follows by allowing any positive finite budget. -/
theorem preparedCorrection_nonempty (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) : Nonempty (PreparedCorrection d.toCorrectionGeometry) := by
  obtain ⟨c,_⟩ := d.preparedCorrection_large hF 0
  exact ⟨c⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
