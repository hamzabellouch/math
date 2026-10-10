import OAI.Geometry.SurfaceImmersion.Atlas.LinearMetricChartReconstruction
import OAI.Geometry.Immersion.ClosedSurface.TensorBounds
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds
import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialBounds
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm

namespace OAI

/-! Uniform atlas estimate for the actual mixed metric and quadratic correction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

local instance cubicFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance cubicFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance cubicDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance cubicDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance cubicSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cubicSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma planeWeight_square_bound (i : A.centers) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      WeightedEstimates.WeightedBound univ s m C (fun x => (A.planeWeight i x)^2) := by
  let C := supportedWeightedSeminorm (modeSupport (A.chartWeightCompact i)) 1 m
    (A.supportedPlaneWeight i)
  have hC : 0 ≤ C := apply_nonneg _ _
  refine ⟨2^m*C*C,by positivity,?_⟩
  intro s hs hs1
  have hb : WeightedEstimates.WeightedBound univ s m C (A.planeWeight i) :=
    (weightedBound_of_supportedSeminorm 1 m (A.supportedPlaneWeight i)).shrink_scale hs.le hs1
  have hh := hb.mul_real uniqueDiffOn_univ hs.le hC hC
    (A.planeWeight_smooth i).contDiffOn (A.planeWeight_smooth i).contDiffOn hb
  simpa only [pow_two] using hh

theorem global_cubic_remainder_bound (m : ℕ) (A₀ B₀ : ℝ) (hA : 0 ≤ A₀) (hB : 0 ≤ B₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (τ δ : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ δ → δ ≤ τ →
      ∀ (U V : M → Space), ContMDiff planeModel spaceModel ∞ U →
      ContMDiff planeModel spaceModel ∞ V →
      A.WeightedBound τ (m+1) (A₀*(δ*τ)) U →
      A.WeightedBound τ (m+1) (B₀*δ^2) V →
      A.TensorWeightedBound τ m (D*(δ^3/τ)) (linearMetricTensor U V + inducedTensor V) := by
  classical
  choose E hE he using fun i : A.centers => A.vectorPlaneRead_bound (V := Space) i (m+1)
  choose Q hQ hq using fun i : A.centers => A.planeWeight_square_bound i m
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  let L : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖
  let C := fun i : A.centers => L*E i
  let B := fun i : A.centers => 4*2^m*(2*(C i*A₀)*(C i*B₀)+(C i*B₀)^2)
  let K := fun i : A.centers => 2^m*Q i*B i
  have hC (i) : 0 ≤ C i := mul_nonneg (norm_nonneg _) (hE i)
  have hB' (i) : 0 ≤ B i := by
    have hc := hC i
    dsimp [B]
    positivity
  have hK (i) : 0 ≤ K i := by
    have hb := hB' i
    have hqi := hQ i
    dsimp [K]
    positivity
  have hsum : 0 ≤ ∑ i, K i := Finset.sum_nonneg (fun i _ => hK i)
  refine ⟨D*∑ i, K i,mul_nonneg hD (Finset.sum_nonneg (fun i _ => hK i)),?_⟩
  intro τ δ hτ hτ1 hδ hδτ U V hU hV hbU hbV
  have hreadU (i) := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hU)
  have hreadV (i) := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hV)
  have hbu (i) : WeightedEstimates.WeightedBound univ τ (m+1) ((C i*A₀)*δ*τ)
      (spaceCoordinates ∘ A.vectorPlaneRead i U) := by
    have hh := (he i U τ (A₀*(δ*τ)) hτ hτ1 (by positivity) hU hbU).linear
      uniqueDiffOn_univ hτ.le (A.vectorPlaneRead_smooth i hU).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    convert hh using 1 <;> dsimp [C,L]
    all_goals ring
  have hbv (i) : WeightedEstimates.WeightedBound univ τ (m+1) ((C i*B₀)*δ^2)
      (spaceCoordinates ∘ A.vectorPlaneRead i V) := by
    have hh := (he i V τ (B₀*δ^2) hτ hτ1 (by positivity) hV hbV).linear
      uniqueDiffOn_univ hτ.le (A.vectorPlaneRead_smooth i hV).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    convert hh using 1 <;> dsimp [C,L]
    all_goals ring
  let T := fun i x => RealModes.realLinearizedTensor
      (spaceCoordinates ∘ A.vectorPlaneRead i U) (spaceCoordinates ∘ A.vectorPlaneRead i V) x +
      RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i V) x
  have hT (i) : ContDiff ℝ ∞ (T i) := contDiffOn_univ.mp
    ((RealModes.contDiffOn_realLinearizedTensor isOpen_univ (hreadU i).contDiffOn
      (hreadV i).contDiffOn).add (RealModes.contDiffOn_realMetricTensor isOpen_univ (hreadV i).contDiffOn))
  have hbT (i) : WeightedEstimates.WeightedBound univ τ m (B i*(δ^3/τ)) (T i) := by
    exact RealModes.weighted_cubic_remainder isOpen_univ hτ hδ hδτ
      (mul_nonneg (hC i) hA) (mul_nonneg (hC i) hB)
      (hreadU i).contDiffOn (hreadV i).contDiffOn (hbu i) (hbv i)
  have hprod (i) : WeightedEstimates.WeightedBound univ τ m
      ((∑ j, K j)*(δ^3/τ)) (fun x => (A.planeWeight i x)^2 • T i x) := by
    have hh := (hq i τ hτ hτ1).smul_real uniqueDiffOn_univ hτ.le (hQ i)
      (mul_nonneg (hB' i) (by positivity))
      ((A.planeWeight_smooth i).pow 2).contDiffOn (hT i).contDiffOn (hbT i)
    apply hh.mono_const
    calc
      2^m*Q i*(B i*(δ^3/τ)) = K i*(δ^3/τ) := by dsimp [K]; ring
      _ ≤ (∑ j, K j)*(δ^3/τ) := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)) (by positivity)
  have hout := hd (fun i x => (A.planeWeight i x)^2 • T i x) τ
    ((∑ i, K i)*(δ^3/τ)) hτ hτ1 (by positivity)
    (fun i => ((A.planeWeight_smooth i).pow 2).smul (hT i)) hprod
  have heq : A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 • T i x) =
      linearMetricTensor U V + inducedTensor V := by
    have ht : (fun i x => (A.planeWeight i x)^2 • T i x) =
        (fun i x => (A.planeWeight i x)^2 • RealModes.realLinearizedTensor
          (spaceCoordinates ∘ A.vectorPlaneRead i U) (spaceCoordinates ∘ A.vectorPlaneRead i V) x) +
        (fun i x => (A.planeWeight i x)^2 •
          RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i V) x) := by
      funext i x
      exact smul_add _ _ _
    rw [ht,A.tensorPlaneRestore_add,A.linearMetric_from_chart_reads hU hV,A.metric_from_chart_reads hV]
  rw [heq] at hout
  convert hout using 1
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
