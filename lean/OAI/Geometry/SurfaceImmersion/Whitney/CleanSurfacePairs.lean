import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceRegularPairLocus
import OAI.Geometry.SurfaceImmersion.Geometry.CompactPairAvoidance
import OAI.Geometry.SurfaceImmersion.Whitney.CompactSurfacePairStability
import OAI.Geometry.SurfaceImmersion.Geometry.FrozenPairGeometry

namespace OAI

/-! Regular pairs which additionally have no coincidence involving the
prescribed finite singular set form an open, stable condition. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def cleanSurfacePairs (f : M → ProjectionTarget 3) (S : Set M) : Set (M × M) :=
  regularSurfacePairs f ∩ {z | f z.1 ≠ f z.2 ∨ (z.1 ∉ S ∧ z.2 ∉ S)}

lemma mem_cleanSurfacePairs {f : M → ProjectionTarget 3} {S : Set M} {z : M × M} :
    z ∈ cleanSurfacePairs f S ↔
      (f z.1 = f z.2 → z.1 ∉ S ∧ z.2 ∉ S ∧ Function.Surjective (surfacePairDerivative f z.1 z.2)) := by
  constructor
  · rintro ⟨hr,ha⟩ he
    exact ⟨(ha.resolve_left (not_not.mpr he)).1,(ha.resolve_left (not_not.mpr he)).2,
      hr.resolve_left (not_not.mpr he)⟩
  · intro h
    by_cases he : f z.1 = f z.2
    · have hh := h he
      exact ⟨Or.inr hh.2.2,Or.inr ⟨hh.1,hh.2.1⟩⟩
    · exact ⟨Or.inl he,Or.inl he⟩

variable [IsManifold planeModel ∞ M] [T2Space M]
theorem cleanSurfacePairs_open {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) {S : Set M} (hS : S.Finite) :
    IsOpen (cleanSurfacePairs f S) := by
  have he : IsOpen {z : M × M | f z.1 ≠ f z.2} :=
    (isClosed_eq (hf.continuous.comp continuous_fst) (hf.continuous.comp continuous_snd)).isOpen_compl
  have hs : IsOpen {z : M × M | z.1 ∉ S ∧ z.2 ∉ S} :=
    (hS.isClosed.isOpen_compl.preimage continuous_fst).inter
      (hS.isClosed.isOpen_compl.preimage continuous_snd)
  exact (regularSurfacePairs_open hf).inter (he.union hs)

variable [CompactSpace M]
theorem compact_clean_pair_stability {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {χ : M → ℝ} (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ) (hb : ∀ x, χ x ∈ Icc 0 1)
    {K : Set (M × M)} (hK : IsCompact K) {S : Set M} (hS : S.Finite)
    (hclean : K ⊆ cleanSurfacePairs f S) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → K ⊆ cleanSurfacePairs (surfaceTranslation f χ a) S := by
  have hr : ∀ z ∈ K, f z.1 = f z.2 → Function.Surjective (surfacePairDerivative f z.1 z.2) :=
    fun z hz he => ((mem_cleanSurfacePairs.mp (hclean hz)) he).2.2
  have ha : ∀ z ∈ K, z.1 ∈ S ∨ z.2 ∈ S → f z.1 ≠ f z.2 := by
    intro z hz hS he
    have hh := (mem_cleanSurfacePairs.mp (hclean hz)) he
    rcases hS with h | h
    · exact hh.1 h
    · exact hh.2.1 h
  obtain ⟨δ,hδ,hδr⟩ := compact_surface_pair_stability hf hχ hK hr
  obtain ⟨η,hη,hηa⟩ := compact_finite_pair_avoidance_stability hf.continuous χ hb hK hS ha
  refine ⟨min δ η,lt_min hδ hη,?_⟩
  intro a ha z hz
  apply mem_cleanSurfacePairs.mpr
  intro he
  have hn : ¬ (z.1 ∈ S ∨ z.2 ∈ S) :=
    fun h => hηa a (ha.trans_le (min_le_right _ _)) z hz h he
  exact ⟨(not_or.mp hn).1,(not_or.mp hn).2,hδr a (ha.trans_le (min_le_left _ _)) z hz he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
