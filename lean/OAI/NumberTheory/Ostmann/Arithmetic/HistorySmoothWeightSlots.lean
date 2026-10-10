import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightAtoms

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicSlots HistoryOccurrenceVariables
variable {ι : Type*}

def independentSlot {l : ℕ} (h : History l) : Key h → Option SmallSlot
  | .inl _ => none
  | .inr (.inl i) => some (h.root.small.get i)
  | .inr (.inr i) => some (internalSlot h i)

def AtomSlotsCorrect (slot : ι → Option SmallSlot) (xs : List SmallSlot)
    (f : Fin xs.length → Expr ι) : Prop :=
  ∀ i, ∃ j, f i = .atom j ∧ slot j = some (xs.get i)

theorem atomSlots_reorder (slot : ι → Option SmallSlot) {xs ys : List SmallSlot}
    (hp : xs.Perm ys) (f : Fin xs.length → Expr ι) (hf : AtomSlotsCorrect slot xs f) :
    AtomSlotsCorrect slot ys (reorder hp f) := by
  intro i
  obtain ⟨j,hj,hslot⟩ := hf ((OccurrencePermutation.indexEquiv hp).symm i)
  have he := OccurrencePermutation.get_indexEquiv hp ((OccurrencePermutation.indexEquiv hp).symm i)
  simp only [Equiv.apply_symm_apply] at he
  exact ⟨j,hj,hslot.trans (congrArg some he.symm)⟩

theorem atomSlots_leftPart (slot : ι → Option SmallSlot) {xs ys : List SmallSlot}
    (f : Fin (xs++ys).length → Expr ι) (hf : AtomSlotsCorrect slot (xs++ys) f) :
    AtomSlotsCorrect slot xs (leftPart f) := by
  intro i
  simpa only [leftPart,get_leftIndex] using hf (leftIndex xs ys i)

theorem atomSlots_rightPart (slot : ι → Option SmallSlot) {xs ys : List SmallSlot}
    (f : Fin (xs++ys).length → Expr ι) (hf : AtomSlotsCorrect slot (xs++ys) f) :
    AtomSlotsCorrect slot ys (rightPart f) := by
  intro i
  simpa only [rightPart,get_rightIndex] using hf (rightIndex xs ys i)

theorem atomSlots_append (slot : ι → Option SmallSlot) {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι)
    (hf : AtomSlotsCorrect slot xs f) (hg : AtomSlotsCorrect slot ys g) :
    AtomSlotsCorrect slot (xs++ys) (append f g) := by
  intro i
  let j : Fin (xs.length+ys.length) := Fin.cast (show (xs++ys).length=xs.length+ys.length from List.length_append) i
  have hj : Fin.cast (show (xs++ys).length=xs.length+ys.length from List.length_append).symm j = i := by simp [j]
  rw [← hj]
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simpa [append,Fin.append_left,leftIndex] using hf k
  · simpa [append,Fin.append_right,rightIndex] using hg k

def StateAtomSlots (slot : ι → Option SmallSlot) {a : State} (e : StateExpr a ι) : Prop :=
  AtomSlotsCorrect slot a.small e.small

theorem children_atomSlots (slot : ι → Option SmallSlot)
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι)
    (he : StateAtomSlots slot e) (hc : AtomSlotsCorrect slot u comp) :
    StateAtomSlots slot (leftState hs e comp) ∧ StateAtomSlots slot (rightState hs e comp) := by
  have hsplit := atomSlots_reorder slot (History.supported_small_split hs) e.small he
  exact ⟨atomSlots_reorder slot (History.supported_child_small hs).1.symm _
      (atomSlots_append slot comp _ hc (atomSlots_leftPart slot _ hsplit)),
    atomSlots_reorder slot (History.supported_child_small hs).2.symm _
      (atomSlots_append slot comp _ hc (atomSlots_rightPart slot _ hsplit))⟩

def TreeAtomSlots (slot : ι → Option SmallSlot) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => StateAtomSlots slot e
  | _, .node _ _ _ _ _ left right, e =>
      StateAtomSlots slot e.1 ∧ TreeAtomSlots slot left e.2.1 ∧ TreeAtomSlots slot right e.2.2

theorem encode_atomSlots (slot : ι → Option SmallSlot) {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (he : StateAtomSlots slot e)
    (hc : ∀ i, ∃ j, comp i = .atom j ∧ slot j = some (internalSlot h i)) :
    TreeAtomSlots slot h (encode V outside h hs e comp) := by
  induction h with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
    have hu : AtomSlotsCorrect slot u (fun i => comp (Sum.inl i)) := by
      intro i
      simpa only [internalSlot,Sum.elim_inl] using hc (Sum.inl i)
    have hchild := children_atomSlots slot hs e _ he hu
    refine ⟨he,?_,?_⟩
    · exact ihl (History.supported_left hs) _ _ hchild.1 (fun i => by
        simpa only [internalSlot,Sum.elim_inr,Sum.elim_inl] using hc (Sum.inr (Sum.inl i)))
    · exact ihr (History.supported_right hs) _ _ hchild.2 (fun i => by
        simpa only [internalSlot,Sum.elim_inr] using hc (Sum.inr (Sum.inr i)))

theorem symbolicHistory_atomSlots {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    TreeAtomSlots (independentSlot h) h (symbolicHistory h hs) :=
  encode_atomSlots (independentSlot h) h hs (rootExpr h) (compensationExpr h)
    (fun i => ⟨Sum.inr (Sum.inl i),rfl,rfl⟩) (fun i => ⟨Sum.inr (Sum.inr i),rfl,rfl⟩)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
