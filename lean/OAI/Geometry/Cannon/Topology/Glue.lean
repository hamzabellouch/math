import Mathlib

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonClosedGluing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {κ : Type*} [Finite κ]

def glue (S : κ → Set X) (hS : ∀ i, IsClosed (S i)) (hcover : ⋃ i, S i=univ)
    (f : ∀ i, C(S i,Y))
    (heq : ∀ i j x (hi : x∈S i) (hj : x∈S j), f i ⟨x,hi⟩=f j ⟨x,hj⟩) : C(X,Y) :=
  ⟨Set.liftCover S (fun i => f i) heq hcover,
    (locallyFinite_of_finite S).continuous hcover hS (fun i => by
      rw [continuousOn_iff_continuous_domRestrict]
      simpa +unfoldPartialApp only [Set.domRestrict,Set.liftCover_coe] using (f i).continuous)⟩

@[simp] lemma glue_apply (S : κ → Set X) (hS : ∀ i, IsClosed (S i)) (hcover : ⋃ i, S i=univ)
    (f : ∀ i, C(S i,Y))
    (heq : ∀ i j x (hi : x∈S i) (hj : x∈S j), f i ⟨x,hi⟩=f j ⟨x,hj⟩)
    (i : κ) (x : S i) : glue S hS hcover f heq x = f i x :=
  by
    change Set.liftCover S (fun i => f i) heq hcover x=f i x
    exact Set.liftCover_coe x

end CannonClosedGluing

end
end
end
end
end
end

end OAI
