import OAI.Geometry.SurfaceImmersion.Primitive.CircularMetricSequence
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
local instance prefixFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance prefixFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance prefixDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance prefixDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance prefixSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance prefixSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

omit [CompactSpace M] [T2Space M] in
lemma metric_eq_of_inner_eq {g h : SmoothMetric M} (he : g.inner = h.inner) : g = h := by
  cases g
  cases h
  cases he
  rfl

namespace CircularPrimitiveFamily
variable {B : SmoothingAtlas M} {N : ℕ} (d : CircularPrimitiveFamily B (Fin N))

def totalTensor (p : M) : CovariantTwoTensor p :=
  ∑ a, (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p

def smoothFamily : SmoothPrimitiveFamily (Fin N) d.totalTensor where
  amplitude := d.amplitude
  phase := d.phase
  smoothAmplitude := d.amplitude_smooth
  smoothPhase := d.phase_smooth
  sum_eq _ := rfl

def prefixIndices (k : Fin (N+1)) : Finset (Fin N) :=
  Finset.univ.filter (fun a => a.val < k.val)

lemma prefixIndices_zero : prefixIndices (0 : Fin (N+1)) = ∅ := by
  ext a
  simp [prefixIndices]

lemma prefixIndices_last : prefixIndices (Fin.last N) = Finset.univ := by
  ext a
  simp [prefixIndices]

lemma prefixIndices_step (a : Fin N) : prefixIndices a.succ = insert a (prefixIndices a.castSucc) := by
  ext b
  simp only [prefixIndices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
    Fin.val_succ,Fin.val_castSucc]
  constructor
  · intro h
    by_cases he : b = a
    · exact Or.inl he
    · exact Or.inr (by have hn : b.val ≠ a.val := fun h => he (Fin.ext h); omega)
  · intro h
    rcases h with rfl | h <;> omega

lemma not_mem_prefixIndices (a : Fin N) : a ∉ prefixIndices a.castSucc := by
  simp [prefixIndices]

def prefixMetric (g : SmoothMetric M) (k : Fin (N+1)) : SmoothMetric M :=
  d.smoothFamily.cycleMetric B g 1 0 (prefixIndices k)

omit [T2Space M] in
lemma prefixMetric_inner (g : SmoothMetric M) (k : Fin (N+1)) :
    (d.prefixMetric g k).inner = g.inner +
      (fun p => ∑ a ∈ prefixIndices k, (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p) := by
  funext p
  change g.inner p + (d.smoothFamily.cycleTensor 1 0 (prefixIndices k) p) = _
  simp [SmoothPrimitiveFamily.cycleTensor,SmoothPrimitiveFamily.term,smoothFamily]

omit [T2Space M] in
lemma prefixMetric_zero (g : SmoothMetric M) : d.prefixMetric g 0 = g := by
  apply metric_eq_of_inner_eq
  rw [d.prefixMetric_inner,prefixIndices_zero]
  funext p
  simp

omit [T2Space M] in
lemma prefixMetric_step (g : SmoothMetric M) (a : Fin N) :
    (d.prefixMetric g a.succ).inner = (d.prefixMetric g a.castSucc).inner +
      (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p) := by
  rw [d.prefixMetric_inner,d.prefixMetric_inner,prefixIndices_step]
  funext p
  simp only [Pi.add_apply,Finset.sum_insert (not_mem_prefixIndices a)]
  abel

omit [T2Space M] in
lemma prefixMetric_last (g : SmoothMetric M) :
    (d.prefixMetric g (Fin.last N)).inner = g.inner+d.totalTensor := by
  rw [d.prefixMetric_inner,prefixIndices_last]
  rfl

 theorem realize_total (g h : SmoothMetric M)
    (htarget : h.inner = g.inner+d.totalTensor)
    (hconvex : ∀ a : Fin N, d.ConvexMetric (d.prefixMetric g a.castSucc) a)
    {F : M → Space} (n : PreferredNormal F) (hF : IsSmoothIsometricImmersion M g F)
    (data : MetricGoodPhaseData g F)
    (hgeom : FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) := by
  have hstart : d.prefixMetric g 0 = g := d.prefixMetric_zero g
  have hend : d.prefixMetric g (Fin.last N) = h :=
    metric_eq_of_inner_eq ((d.prefixMetric_last g).trans htarget.symm)
  have hF' : IsSmoothIsometricImmersion M (d.prefixMetric g 0) F := by rwa [hstart]
  have hdata : MetricGoodPhaseData (d.prefixMetric g 0) F := by rwa [hstart]
  obtain ⟨W,hW,hgood,_⟩ := realize_sequence N d (d.prefixMetric g)
    (d.prefixMetric_step g) hconvex F n hF' hdata hgeom
  rw [hend] at hW hgood
  exact ⟨W,hW,hgood⟩

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
