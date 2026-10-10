import OAI.Geometry.SurfaceImmersion.Geometry.UnorderedLinePair

namespace OAI

/-! Applying a function to both entries of an unordered pair. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def unorderedPairMap {M N : Type*} (f : M → N) : UnorderedSurfacePairs M → UnorderedSurfacePairs N :=
  Quotient.map (Prod.map f f) (by
    intro x y h
    rcases h with h | h
    · exact Or.inl (congrArg (Prod.map f f) h)
    · right
      rw [h]
      rfl)

lemma unorderedPairMap_mk {M N : Type*} (f : M → N) (x : M × M) :
    unorderedPairMap f (unorderedPair x) = unorderedPair (Prod.map f f x) := rfl

lemma unorderedPairMap_comp {M N P : Type*} (f : M → N) (g : N → P)
    (x : UnorderedSurfacePairs M) :
    unorderedPairMap g (unorderedPairMap f x) = unorderedPairMap (g ∘ f) x := by
  induction x using Quotient.inductionOn with
  | h x => rfl

lemma unorderedLinePair_interval_embedding (a w : Base) (hw : w ≠ 0) (R : ℝ) :
    IsClosedEmbedding (fun s : Icc (0 : ℝ) R => unorderedLinePair a w s) := by
  apply ((unorderedLinePair_continuous a w).comp continuous_subtype_val).isClosedEmbedding
  intro s t h
  apply Subtype.ext
  exact unorderedLinePair_injOn_nonneg a w hw s.property.1 t.property.1 h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
