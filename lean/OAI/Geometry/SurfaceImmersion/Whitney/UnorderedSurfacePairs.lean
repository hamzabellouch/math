import OAI.Geometry.SurfaceImmersion.Whitney.CompactDoublePairs

namespace OAI

/-! The Hausdorff space of unordered pairs. The quotient identifies only
interchanging the two source points of a double pair. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

def surfacePairSetoid (M : Type*) : Setoid (M × M) where
  r x y := x = y ∨ x = y.swap
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h,Prod.swap_swap])
    trans := by
      intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (hxy.trans hyz)
      · exact Or.inr (hxy.trans (congrArg Prod.swap hyz))
      · exact Or.inl (by rw [hxy,hyz,Prod.swap_swap]) }

abbrev UnorderedSurfacePairs (M : Type*) := Quotient (surfacePairSetoid M)

def unorderedPair {M : Type*} (z : M × M) : UnorderedSurfacePairs M := @Quotient.mk' (M × M) (surfacePairSetoid M) z

lemma unorderedPair_eq {M : Type*} {x y : M × M} :
    unorderedPair x = unorderedPair y ↔ x = y ∨ x = y.swap := @Quotient.eq'' (M × M) (surfacePairSetoid M) x y

lemma unorderedPair_swap {M : Type*} (x : M × M) : unorderedPair x.swap = unorderedPair x :=
  unorderedPair_eq.mpr (Or.inr rfl)

lemma unorderedPair_preimage_image {M : Type*} (U : Set (M × M)) :
    unorderedPair ⁻¹' (unorderedPair '' U) = U ∪ Prod.swap ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨y,hy,hxy⟩
    rcases unorderedPair_eq.mp hxy with h | h
    · exact Or.inl (h ▸ hy)
    · apply Or.inr
      change x.swap ∈ U
      rwa [h] at hy
  · rintro (hx | hx)
    · exact ⟨x,hx,rfl⟩
    · exact ⟨x.swap,hx,unorderedPair_swap x⟩

lemma unorderedPair_continuous {M : Type*} [TopologicalSpace M] :
    Continuous (unorderedPair : M × M → UnorderedSurfacePairs M) := continuous_quotient_mk'

lemma unorderedPair_isOpenMap {M : Type*} [TopologicalSpace M] :
    IsOpenMap (unorderedPair : M × M → UnorderedSurfacePairs M) := by
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (unorderedPair ⁻¹' (unorderedPair '' U))
  rw [unorderedPair_preimage_image]
  exact hU.union (hU.preimage continuous_swap)

lemma unorderedPair_isOpenQuotientMap {M : Type*} [TopologicalSpace M] :
    IsOpenQuotientMap (unorderedPair : M × M → UnorderedSurfacePairs M) :=
  .of_isOpenMap_isQuotientMap unorderedPair_isOpenMap isQuotientMap_quotient_mk'

instance unorderedSurfacePairs_t2 {M : Type*} [TopologicalSpace M] [T2Space M] :
    T2Space (UnorderedSurfacePairs M) := by
  apply (t2Space_iff_of_isOpenQuotientMap unorderedPair_isOpenQuotientMap).mpr
  have he : {z : (M × M) × (M × M) | unorderedPair z.1 = unorderedPair z.2} =
      {z | z.1 = z.2} ∪ {z | z.1 = z.2.swap} := by
    ext z
    exact unorderedPair_eq
  rw [he]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst (continuous_swap.comp continuous_snd))

lemma unorderedPair_injOn_product {M : Type*} {U V : Set M} (hd : Disjoint U V) :
    (U ×ˢ V).InjOn (unorderedPair : M × M → UnorderedSurfacePairs M) := by
  intro x hx y hy he
  rcases unorderedPair_eq.mp he with he | he
  · exact he
  · exfalso
    have hfst : x.1 = y.2 := congrArg Prod.fst he
    exact Set.disjoint_left.mp hd hx.1 (hfst ▸ hy.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
