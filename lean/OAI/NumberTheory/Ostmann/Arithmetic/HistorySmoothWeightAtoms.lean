import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRegular

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicSlots
open HistoryOccurrenceVariables
variable {ι : Type*}

def StateSmallAtoms {a : State} (e : StateExpr a ι) : Prop :=
  ∀ i, ∃ j, e.small i = .atom j

theorem children_smallAtoms {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι)
    (he : StateSmallAtoms e) (hc : ∀ i, ∃ j, comp i = .atom j) :
    StateSmallAtoms (leftState hs e comp) ∧ StateSmallAtoms (rightState hs e comp) := by
  have hleft : ∀ i, ∃ j, leftPart (splitSlots hs e) i = .atom j := fun i => he _
  have hright : ∀ i, ∃ j, rightPart (splitSlots hs e) i = .atom j := fun i => he _
  exact ⟨(fun i => append_forall (fun z => ∃ j, z = .atom j) comp _ hc hleft _),
    (fun i => append_forall (fun z => ∃ j, z = .atom j) comp _ hc hright _)⟩

def TreeSmallAtoms : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => StateSmallAtoms e
  | _, .node _ _ _ _ _ left right, e =>
      StateSmallAtoms e.1 ∧ TreeSmallAtoms left e.2.1 ∧ TreeSmallAtoms right e.2.2

theorem encode_smallAtoms {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (he : StateSmallAtoms e)
    (hc : ∀ i, ∃ j, comp i = .atom j) : TreeSmallAtoms h (encode V outside h hs e comp) := by
  induction h with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
    have hchild := children_smallAtoms hs e (fun i => comp (Sum.inl i)) he (fun i => hc (Sum.inl i))
    exact ⟨he,ihl (History.supported_left hs) _ _ hchild.1 (fun i => hc (Sum.inr (Sum.inl i))),
      ihr (History.supported_right hs) _ _ hchild.2 (fun i => hc (Sum.inr (Sum.inr i)))⟩

theorem symbolicHistory_smallAtoms {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) : TreeSmallAtoms h (symbolicHistory h hs) :=
  encode_smallAtoms h hs (rootExpr h) (compensationExpr h)
    (fun i => ⟨Sum.inr (Sum.inl i),rfl⟩) (fun i => ⟨Sum.inr (Sum.inr i),rfl⟩)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
