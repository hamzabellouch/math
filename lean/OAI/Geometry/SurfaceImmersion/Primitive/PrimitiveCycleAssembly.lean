import OAI.Geometry.SurfaceImmersion.Correction.SmoothPrimitiveFamily

namespace OAI

/-! Exact finite-cycle identities for independently chosen primitive families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance assemblyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance assemblyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance assemblyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance assemblyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance assemblySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance assemblySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u)

def cycleAmplitude (N : ℕ) (a : ι) (p : M) : ℝ :=
  d.amplitude a p/Real.sqrt (N : ℝ)

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleAmplitude_square (N : ℕ) (a : ι) (p : M) :
    (d.cycleAmplitude N a p)^2 = (N : ℝ)⁻¹*(d.amplitude a p)^2 := by
  rw [cycleAmplitude,div_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  exact div_eq_inv_mul _ _

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleAmplitude_smooth (N : ℕ) (a : ι) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (d.cycleAmplitude N a) :=
  (d.smoothAmplitude a).div_const _

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleAmplitude_pos_iff {N : ℕ} (hN : 0 < N) (a : ι) (p : M) :
    0 < d.cycleAmplitude N a p ↔ 0 < d.amplitude a p :=
  div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (by exact_mod_cast hN))

lemma cycleMetric_start (A : SmoothingAtlas M) (g : SmoothMetric M) (N : ℕ) :
    (d.cycleMetric A g N 0 ∅).inner = g.inner := by
  funext p
  change g.inner p+d.cycleTensor N 0 ∅ p = g.inner p
  rw [d.cycleTensor_empty]
  simp

lemma cycleMetric_step [DecidableEq ι] (A : SmoothingAtlas M) (g : SmoothMetric M)
    (N c : ℕ) (s : Finset ι) (a : ι) (ha : a ∉ s) (p : M)
    (v w : TangentSpace planeModel p) :
    (d.cycleMetric A g N c (insert a s)).inner p v w =
      (d.cycleMetric A g N c s).inner p v w+(d.cycleAmplitude N a p)^2*
        (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p v)*
        (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p w) := by
  change (g.inner p+d.cycleTensor N c (insert a s) p) v w = _
  rw [d.cycleTensor_insert N c s a ha p]
  change g.inner p v w+(d.cycleTensor N c s p v w+(N : ℝ)⁻¹*d.term a p v w) = _
  rw [d.term_apply,d.cycleAmplitude_square]
  change g.inner p v w+(_+_) = (g.inner p v w+d.cycleTensor N c s p v w)+_
  ring

lemma cycleMetric_next (e : SmoothPrimitiveFamily ι u) (A : SmoothingAtlas M)
    (g : SmoothMetric M) (N c : ℕ) :
    (d.cycleMetric A g N c Finset.univ).inner = (e.cycleMetric A g N (c+1) ∅).inner := by
  funext p
  change g.inner p+d.cycleTensor N c Finset.univ p = g.inner p+e.cycleTensor N (c+1) ∅ p
  rw [d.cycleTensor_complete,e.cycleTensor_empty]

lemma cycleMetric_finish (A : SmoothingAtlas M) (g : SmoothMetric M) {N : ℕ} (hN : 0 < N) :
    (d.cycleMetric A g N N ∅).inner = g.inner+u := by
  funext p
  change g.inner p+d.cycleTensor N N ∅ p = g.inner p+u p
  rw [d.cycleTensor_empty,div_self (by exact_mod_cast (Nat.ne_of_gt hN)),one_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily

end

end OAI
