import OAI.NumberTheory.DukePrimeDegree.Geometry.RootTransverseRectangles

namespace OAI

/-! # Root boxes around compact transverse families in one free orbit -/

noncomputable section
open Matrix Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootBox_contains_compact_transverse {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (S : Set (RootSlice a b k)) (hS : IsCompact S)
    (hinj : Set.InjOn (rootQuotientParametrization hab) (S ×ˢ univ))
    (I : Set ℝ) (hI : IsCompact I) :
    ∃ A : RootBox hab k, S ⊆ A.transverse ∧ I ⊆ A.time := by
  obtain ⟨W,hW,hSW,hemb⟩ := compact_injective_localHomeomorph_neighborhood
    (rootQuotientParametrization_localHomeomorph hab) (hS.prod hI)
      (hinj.mono (prod_mono_right (subset_univ I)))
  obtain ⟨U,V,hU,hV,hSU,hIV,hUV⟩ := generalized_tube_lemma hS hI hW hSW
  have he := hemb.comp (Topology.IsOpenEmbedding.inclusion hUV
    ((hU.prod hV).preimage continuous_subtype_val))
  exact ⟨⟨U,V,hU,hV,he⟩,hSU,hIV⟩

end DukePrimeDegree

end

end OAI
