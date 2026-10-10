import OAI.Probability.ClassicalON.PinnedSigns

namespace OAI

universe uE uV

noncomputable section
open scoped Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE}

def bondGraph (left right : E → V) (η : E → Bool) : SimpleGraph V where
  Adj x y := x≠y ∧ ∃ e,η e=true ∧
    ((left e=x ∧ right e=y) ∨ (left e=y ∧ right e=x))
  symm := ⟨by
    intro x y ⟨h,e,he,hor⟩
    exact ⟨h.symm,e,he,hor.elim (fun ⟨a,b⟩ => Or.inr ⟨a,b⟩) (fun ⟨a,b⟩ => Or.inl ⟨a,b⟩)⟩⟩
  loopless := ⟨by intro x; simp⟩

theorem bondGraph_endpoint_reachable (left right : E → V) (η : E → Bool) (e : E)
    (he : η e=true) : (bondGraph left right η).Reachable (left e) (right e) := by
  by_cases h : left e=right e
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h,e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem bondConnected_iff_reachable (left right : E → V) (η : E → Bool) (x y : V) :
    bondConnected left right η x y ↔ (bondGraph left right η).Reachable x y := by
  constructor
  · intro h
    let s : V → SignField := fun v => if (bondGraph left right η).Reachable x v then 0 else 1
    have hs : s∈bondSubspace left right η := by
      intro e he
      have hh := bondGraph_endpoint_reachable left right η e he
      have hi : (bondGraph left right η).Reachable x (left e) ↔
          (bondGraph left right η).Reachable x (right e) :=
        ⟨fun hp => hp.trans hh,fun hp => hp.trans hh.symm⟩
      simp only [s,hi]
    have hh := h s hs
    by_contra hy
    simp [s,hy] at hh
  · rintro ⟨p⟩ s hs
    induction p with
    | nil => rfl
    | @cons u v w huv p ih =>
      apply Eq.trans _ ih
      obtain ⟨_,e,he,hor⟩ := huv
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hs e he
      · exact (hs e he).symm

end ClassicalON

end

end OAI
