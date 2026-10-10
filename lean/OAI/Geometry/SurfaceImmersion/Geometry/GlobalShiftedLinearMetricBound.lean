import OAI.Geometry.SurfaceImmersion.Geometry.GlobalCubicRemainder
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadPrefixBounds
import OAI.Geometry.SurfaceImmersion.Geometry.LinearMetricDerivativeBounds

namespace OAI

/-! The mixed metric uses the unweighted derivative prefix of its first input. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance shiftedLinearBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance shiftedLinearBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance shiftedLinearBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance shiftedLinearBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance shiftedLinearBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance shiftedLinearBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem global_shifted_linear_metric_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (τ a b : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ a → 0 ≤ b →
      ∀ (U V : M → Space), ContMDiff planeModel spaceModel ∞ U →
      ContMDiff planeModel spaceModel ∞ V →
      A.ShiftedBound 1 m τ a U → A.WeightedBound τ (m+1) b V →
      A.TensorWeightedBound τ m (D*(a*b/τ)) (linearMetricTensor U V) := by
  classical
  choose E hE he using fun i : A.centers => A.vectorPlaneRead_prefix_bounds (V := Space) i 1 m
  choose E' hE' he' using fun i : A.centers => A.vectorPlaneRead_bound (V := Space) i (m+1)
  choose Q hQ hq using fun i : A.centers => A.planeWeight_square_bound i m
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  let L : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖
  let C := fun i : A.centers => L*E i
  let C' := fun i : A.centers => L*E' i
  let B := fun i : A.centers => 8*2^m*C i*C' i
  let K := fun i : A.centers => 2^m*Q i*B i
  have hC (i) : 0 ≤ C i := mul_nonneg (norm_nonneg _) (hE i)
  have hC' (i) : 0 ≤ C' i := mul_nonneg (norm_nonneg _) (hE' i)
  have hB (i) : 0 ≤ B i := by
    have hc := hC i
    have hc' := hC' i
    dsimp [B]
    positivity
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
      WeightedEstimates.WeightedBound univ τ (m+1) (C' i*c) (spaceCoordinates ∘ A.vectorPlaneRead i X) := by
    have hh := (he' i X τ c hτ hτ1 hc hX hx).linear uniqueDiffOn_univ hτ.le
      (A.vectorPlaneRead_smooth i hX).contDiffOn spaceCoordinates.toContinuousLinearMap
    convert hh using 1 <;> dsimp [C',L]
    all_goals ring
  have hreadU (i : A.centers) (v : SmallModes.Base) (hv : ‖v‖ ≤ 1) :
      WeightedEstimates.WeightedBound univ τ m (C i*a)
        (SmallModes.coordDeriv v (spaceCoordinates ∘ A.vectorPlaneRead i U)) := by
    apply prefix_directional_bound
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hU)) hτ (mul_nonneg (hC i) ha)
      (v := v) (hv := hv)
    intro j hj
    have hh := (he i U τ a hτ hτ1 ha hU hbU j (by omega)).linear
      uniqueDiffOn_univ (by norm_num : (0:ℝ) ≤ 1)
      (A.vectorPlaneRead_smooth i hU).contDiffOn spaceCoordinates.toContinuousLinearMap
    convert hh using 1 <;> dsimp [C,L]
    all_goals ring
  let T := fun i => RealModes.realLinearizedTensor
    (spaceCoordinates ∘ A.vectorPlaneRead i U) (spaceCoordinates ∘ A.vectorPlaneRead i V)
  have hT (i) : ContDiff ℝ ∞ (T i) := contDiffOn_univ.mp
    (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hU)).contDiffOn
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hV)).contDiffOn)
  have hbT (i) : WeightedEstimates.WeightedBound univ τ m (B i*(a*b/τ)) (T i) := by
    have hc' := hC' i
    have hreadV (v : SmallModes.Base) (hv : ‖v‖ ≤ 1) :
        WeightedEstimates.WeightedBound univ τ m (C' i*b/τ)
          (SmallModes.coordDeriv v (spaceCoordinates ∘ A.vectorPlaneRead i V)) := by
      exact ((hread V hV b hb hbV i).directional isOpen_univ hτ
        (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hV)).contDiffOn v).mono_const
        (mul_le_of_le_one_left (by positivity) hv)
    have hh := RealModes.weighted_realLinearizedTensor_of_derivatives isOpen_univ hτ
      (mul_nonneg (hC i) ha) (by positivity : 0 ≤ C' i*b/τ)
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hU)).contDiffOn
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hV)).contDiffOn
      (hreadU i) hreadV
    have heq : 2*((4:ℕ):ℝ)*(2^m*(C i*a)*(C' i*b/τ)) = B i*(a*b/τ) := by
      dsimp [B]
      field_simp
      ring
    rw [heq] at hh
    exact hh
  have hprod (i) : WeightedEstimates.WeightedBound univ τ m
      ((∑ j, K j)*(a*b/τ)) (fun x => (A.planeWeight i x)^2 • T i x) := by
    have hh := (hq i τ hτ hτ1).smul_real uniqueDiffOn_univ hτ.le (hQ i)
      (mul_nonneg (hB i) (by positivity))
      ((A.planeWeight_smooth i).pow 2).contDiffOn (hT i).contDiffOn (hbT i)
    apply hh.mono_const
    calc
      2^m*Q i*(B i*(a*b/τ)) = K i*(a*b/τ) := by dsimp [K]; ring
      _ ≤ (∑ j, K j)*(a*b/τ) := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)) (by positivity)
  have hout := hd (fun i x => (A.planeWeight i x)^2 • T i x) τ
    ((∑ i, K i)*(a*b/τ)) hτ hτ1 (by positivity)
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
