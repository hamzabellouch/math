import OAI.Geometry.SurfaceImmersion.Geometry.FiniteCycleOrder
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCycleAssembly

namespace OAI

/-! The actual ordered prefix metrics of a finite circular family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance flatCycleFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance flatCycleFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance flatCycleDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance flatCycleDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance flatCycleSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance flatCycleSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace CircularPrimitiveFamily
variable {B : SmoothingAtlas M} {N m : ℕ}
    (d : CircularPrimitiveFamily B (Fin (N*m)))
    {u : ∀ p : M, CovariantTwoTensor p}
    (f : Fin N → SmoothPrimitiveFamily (Fin m) u)
    (ha : ∀ a p, d.amplitude a p = (f a.divNat).cycleAmplitude N a.modNat p)
    (hp : ∀ a, d.phase a = (f a.divNat).phase a.modNat)

include f ha hp

omit [CompactSpace M] [T2Space M] in
lemma flat_cycle_term (a : Fin (N*m)) (p : M) :
    (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p =
      (N : ℝ)⁻¹ • (f a.divNat).term a.modNat p := by
  rw [ha,hp,SmoothPrimitiveFamily.cycleAmplitude_square]
  simp only [SmoothPrimitiveFamily.term,smul_smul]

omit [T2Space M] in
lemma prefixMetric_cycle (g : SmoothMetric M) (k : Fin N) (j : Fin m) :
    d.prefixMetric g (finProdFinEquiv (k,j)).castSucc =
      (f k).cycleMetric B g N k.val (prefixIndices j.castSucc) := by
  apply metric_eq_of_inner_eq
  rw [d.prefixMetric_inner]
  funext p
  change g.inner p + _ = g.inner p + (f k).cycleTensor N k.val (prefixIndices j.castSucc) p
  congr 1
  simp_rw [d.flat_cycle_term f ha hp]
  rw [← Finset.smul_sum]
  rw [finite_cycle_prefix_sum (fun a b => (f a).term b p) (u p)
    (fun a => (f a).sum_eq p) k j]
  rw [smul_add,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  change ((N : ℝ)⁻¹ * (k.val : ℝ)) • u p + _ = _
  rw [mul_comm]
  rfl

omit [CompactSpace M] [T2Space M] in
lemma totalTensor_cycle (hN : 0 < N) : d.totalTensor = u := by
  funext p
  change (∑ a, (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p) = u p
  simp_rw [d.flat_cycle_term f ha hp]
  rw [← Finset.smul_sum,finite_cycle_total_sum (fun a b => (f a).term b p) (u p)
    (fun a => (f a).sum_eq p),← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hN)),one_smul]

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
