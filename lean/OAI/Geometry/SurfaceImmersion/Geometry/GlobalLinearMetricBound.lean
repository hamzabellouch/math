import OAI.Geometry.SurfaceImmersion.Geometry.GlobalCubicRemainder

namespace OAI

/-! The true global mixed metric is bilinear in its two weighted input bounds. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance linearBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance linearBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance linearBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance linearBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance linearBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance linearBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem global_linear_metric_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (τ a b : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ a → 0 ≤ b →
      ∀ (U V : M → Space), ContMDiff planeModel spaceModel ∞ U →
      ContMDiff planeModel spaceModel ∞ V →
      A.WeightedBound τ (m+1) a U → A.WeightedBound τ (m+1) b V →
      A.TensorWeightedBound τ m (D*(a*b/τ^2)) (linearMetricTensor U V) := by
  classical
  choose E hE he using fun i : A.centers => A.vectorPlaneRead_bound (V := Space) i (m+1)
  choose Q hQ hq using fun i : A.centers => A.planeWeight_square_bound i m
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  let L : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖
  let C := fun i : A.centers => L*E i
  let B := fun i : A.centers => 8*2^m*(C i)^2
  let K := fun i : A.centers => 2^m*Q i*B i
  have hC (i) : 0 ≤ C i := mul_nonneg (norm_nonneg _) (hE i)
  have hB (i) : 0 ≤ B i := by dsimp [B]; positivity
  have hK (i) : 0 ≤ K i := by
    have hbi := hB i
    have hqi := hQ i
    dsimp [K]
    positivity
  have hsum : 0 ≤ ∑ i, K i := Finset.sum_nonneg (fun i _ => hK i)
  refine ⟨D*∑ i, K i,mul_nonneg hD hsum,?_⟩
  intro τ a b hτ hτ1 ha hb U V hU hV hbU hbV
  have hread (X : M → Space) (hX : ContMDiff planeModel spaceModel ∞ X)
      (c : ℝ) (hc : 0 ≤ c) (hx : A.WeightedBound τ (m+1) c X) (i : A.centers) :
      WeightedEstimates.WeightedBound univ τ (m+1) (C i*c) (spaceCoordinates ∘ A.vectorPlaneRead i X) := by
    have hh := (he i X τ c hτ hτ1 hc hX hx).linear uniqueDiffOn_univ hτ.le
      (A.vectorPlaneRead_smooth i hX).contDiffOn spaceCoordinates.toContinuousLinearMap
    convert hh using 1 <;> dsimp [C,L]
    all_goals ring
  let T := fun i => RealModes.realLinearizedTensor
    (spaceCoordinates ∘ A.vectorPlaneRead i U) (spaceCoordinates ∘ A.vectorPlaneRead i V)
  have hT (i) : ContDiff ℝ ∞ (T i) := contDiffOn_univ.mp
    (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hU)).contDiffOn
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hV)).contDiffOn)
  have hbT (i) : WeightedEstimates.WeightedBound univ τ m (B i*(a*b/τ^2)) (T i) := by
    have hh := RealModes.weighted_realLinearizedTensor isOpen_univ hτ
      (mul_nonneg (hC i) ha) (mul_nonneg (hC i) hb)
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hU)).contDiffOn
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hV)).contDiffOn
      (hread U hU a ha hbU i) (hread V hV b hb hbV i)
    have heq : 2*((4:ℕ):ℝ)*(2^m*(C i*a/τ)*(C i*b/τ)) = B i*(a*b/τ^2) := by
      dsimp [B]
      field_simp
      ring
    rw [heq] at hh
    exact hh
  have hprod (i) : WeightedEstimates.WeightedBound univ τ m
      ((∑ j, K j)*(a*b/τ^2)) (fun x => (A.planeWeight i x)^2 • T i x) := by
    have hh := (hq i τ hτ hτ1).smul_real uniqueDiffOn_univ hτ.le (hQ i)
      (mul_nonneg (hB i) (by positivity))
      ((A.planeWeight_smooth i).pow 2).contDiffOn (hT i).contDiffOn (hbT i)
    apply hh.mono_const
    calc
      2^m*Q i*(B i*(a*b/τ^2)) = K i*(a*b/τ^2) := by dsimp [K]; ring
      _ ≤ (∑ j, K j)*(a*b/τ^2) := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)) (by positivity)
  have hout := hd (fun i x => (A.planeWeight i x)^2 • T i x) τ
    ((∑ i, K i)*(a*b/τ^2)) hτ hτ1 (by positivity)
    (fun i => ((A.planeWeight_smooth i).pow 2).smul (hT i)) hprod
  have heq : A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 • T i x) = linearMetricTensor U V :=
    A.linearMetric_from_chart_reads hU hV
  rw [heq] at hout
  convert hout using 1
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
