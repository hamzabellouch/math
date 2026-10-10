import OAI.Geometry.SurfaceImmersion.Geometry.ImmersionLocalInjectivity

namespace OAI

/-! The compactification of the double-pair locus can meet the diagonal
only at singular points. Removing open crosscap neighborhoods leaves a
compact set of genuine distinct double pairs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfaceDoublePairs (f : M → ProjectionTarget 3) : Set (M × M) :=
  {z | z.1 ≠ z.2 ∧ f z.1 = f z.2}

lemma doublePairs_closure_diagonal_singular {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) (p : M)
    (hp : (p,p) ∈ closure (surfaceDoublePairs f)) :
    ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) := by
  intro hreg
  obtain ⟨U,hU,hpU,hI⟩ := surface_immersion_local_injective hf p hreg
  obtain ⟨z,hzU,hzD⟩ := (_root_.mem_closure_iff.mp hp) (U ×ˢ U) (hU.prod hU) ⟨hpU,hpU⟩
  exact hzD.1 (hI hzU.1 hzU.2 hzD.2)

omit [ChartedSpace Plane M] [IsManifold planeModel ∞ M] in
lemma doublePairs_closure_equal {f : M → ProjectionTarget 3}
    (hf : Continuous f) : closure (surfaceDoublePairs f) ⊆ {z | f z.1 = f z.2} :=
  closure_minimal (fun _ hz => hz.2)
    (isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd))

theorem compact_doublePairs_exterior [CompactSpace M] {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {ι : Type*} (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ i, p ∈ U i) :
    IsCompact (closure (surfaceDoublePairs f) \ ⋃ i, U i ×ˢ U i) ∧
      closure (surfaceDoublePairs f) \ (⋃ i, U i ×ˢ U i) ⊆ surfaceDoublePairs f := by
  refine ⟨isClosed_closure.isCompact.diff (isOpen_iUnion fun i => (hU i).prod (hU i)),?_⟩
  intro z hz
  refine ⟨?_,doublePairs_closure_equal hf.continuous hz.1⟩
  intro heq
  have hzdiag : (z.1,z.1) ∈ closure (surfaceDoublePairs f) := by
    have he : (z.1,z.1) = z := Prod.ext rfl heq
    rw [he]
    exact hz.1
  obtain ⟨i,hi⟩ := hcover z.1 (doublePairs_closure_diagonal_singular hf z.1 hzdiag)
  apply hz.2
  exact mem_iUnion.mpr ⟨i,hi,heq ▸ hi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
