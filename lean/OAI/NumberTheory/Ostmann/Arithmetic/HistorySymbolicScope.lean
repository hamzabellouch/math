import OAI.NumberTheory.Ostmann.Arithmetic.HistoryOccurrenceLevels
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicEncoding
import OAI.NumberTheory.Ostmann.Characters.RationalHistoryVariables

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicScope
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicSlots

variable {ι : Type*}

def Above (level : ι → ℕ) (t : ℕ) : Expr ι → Prop
  | .atom i => t < level i
  | .fixed _ => True
  | .add a b | .sub a b | .mul a b | .divide a b => Above level t a ∧ Above level t b

theorem above_mono {level : ι → ℕ} {t s : ℕ} (ht : t ≤ s) (e : Expr ι)
    (h : Above level s e) : Above level t e := by
  induction e with
  | atom i => exact lt_of_le_of_lt ht h
  | fixed c => trivial
  | add a b ia ib | sub a b ia ib | mul a b ia ib | divide a b ia ib =>
      exact ⟨ia h.1,ib h.2⟩

theorem above_atoms {level : ι → ℕ} {t : ℕ} [DecidableEq ι]
    (e : Expr ι) (h : Above level t e) : ∀ i ∈ e.atoms, t < level i := by
  induction e with
  | atom j =>
      intro i hi
      have hij : i = j := Finset.mem_singleton.mp hi
      simpa only [hij,Above] using h
  | fixed c => simp [Expr.atoms]
  | add a b ia ib | sub a b ia ib | mul a b ia ib | divide a b ia ib =>
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact ia h.1 i hi
      · exact ib h.2 i hi

theorem product_above {level : ι → ℕ} {t : ℕ} (es : List (Expr ι))
    (h : ∀ e ∈ es, Above level t e) : Above level t (HistorySymbolicStep.product es) := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp),ih (fun z hz => h z (by simp [hz]))⟩

theorem product_ofFn_above {level : ι → ℕ} {t n : ℕ} (f : Fin n → Expr ι)
    (h : ∀ i, Above level t (f i)) : Above level t (HistorySymbolicStep.product (List.ofFn f)) := by
  apply product_above
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact h i

def StateAbove (level : ι → ℕ) (t : ℕ) {a : State} (e : StateExpr a ι) : Prop :=
  Above level t e.plus ∧ Above level t e.minus ∧ ∀ i, Above level t (e.small i)

theorem stateAbove_mono {level : ι → ℕ} {t s : ℕ} (ht : t ≤ s)
    {a : State} (e : StateExpr a ι) (h : StateAbove level s e) : StateAbove level t e :=
  ⟨above_mono ht _ h.1,above_mono ht _ h.2.1,fun i => above_mono ht _ (h.2.2 i)⟩

theorem reorder_above {level : ι → ℕ} {t : ℕ} {xs ys : List SmallSlot}
    (hp : xs.Perm ys) (f : Fin xs.length → Expr ι)
    (h : ∀ i, Above level t (f i)) : ∀ i, Above level t (reorder hp f i) :=
  fun _ => h _

theorem append_above {level : ι → ℕ} {t : ℕ} {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι)
    (hf : ∀ i, Above level t (f i)) (hg : ∀ i, Above level t (g i)) :
    ∀ i, Above level t (append f g i) := by
  intro i
  change Above level t (Fin.append f g _)
  refine Fin.addCases (motive := fun j : Fin (xs.length+ys.length) =>
    Above level t (Fin.append f g j)) ?_ ?_ _
  · intro j
    simpa only [Fin.append_left] using hf j
  · intro j
    simpa only [Fin.append_right] using hg j

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem child_above (hs : (History.node a p u hp hm left right).Supported V outside)
    (level : ι → ℕ) (e : StateExpr a ι) (comp : Fin u.length → Expr ι)
    (he : StateAbove level (l+1) e) (hc : ∀ i, Above level l (comp i)) :
    StateAbove level l (leftState hs e comp) ∧ StateAbove level l (rightState hs e comp) := by
  have he' := stateAbove_mono (Nat.le_succ l) e he
  have hsplit := reorder_above (History.supported_small_split hs) e.small he'.2.2
  have hleft : ∀ i, Above level l (leftPart (splitSlots hs e) i) := fun i => hsplit _
  have hright : ∀ i, Above level l (rightPart (splitSlots hs e) i) := fun i => hsplit _
  have hU := product_ofFn_above comp hc
  have hP := product_ofFn_above _ hleft
  have hM := product_ofFn_above _ hright
  have hPivot : Above level l (pivotExpr hs e comp) :=
    ⟨⟨⟨trivial,he'.2.1,hM⟩,⟨trivial,he'.1,hP⟩⟩,⟨trivial,hU⟩⟩
  constructor
  · exact ⟨hPivot,he'.1,reorder_above (History.supported_child_small hs).1.symm _
      (append_above comp _ hc hleft)⟩
  · exact ⟨hPivot,he'.2.1,reorder_above (History.supported_child_small hs).2.symm _
      (append_above comp _ hc hright)⟩

def TreeAbove (level : ι → ℕ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => StateAbove level 0 e
  | l+1, .node _ _ _ _ _ left right, e =>
      StateAbove level (l+1) e.1 ∧ TreeAbove level left e.2.1 ∧ TreeAbove level right e.2.2

theorem encode_above {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (level : ι → ℕ)
    (e : StateExpr h.root ι) (comp : InternalKey h → Expr ι)
    (he : StateAbove level l e)
    (hc : ∀ i, Above level (internalLevel h i - 1) (comp i)) :
    TreeAbove level h (encode V outside h hs e comp) := by
  induction h with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
      have hu : ∀ i, Above level l (comp (Sum.inl i)) := by
        intro i
        simpa only [internalLevel,Sum.elim_inl,Nat.add_sub_cancel] using hc (Sum.inl i)
      have hchildren := child_above hs level e _ he hu
      refine ⟨he,?_,?_⟩
      · exact ihl (History.supported_left hs) _ _ hchildren.1 (fun i =>
          hc (Sum.inr (Sum.inl i)))
      · exact ihr (History.supported_right hs) _ _ hchildren.2 (fun i =>
          hc (Sum.inr (Sum.inr i)))

theorem symbolicHistory_above {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    TreeAbove (keyLevel h) h (symbolicHistory h hs) := by
  apply encode_above
  · exact ⟨Nat.lt_succ_self l,Nat.lt_succ_self l,fun _ => Nat.lt_succ_self l⟩
  · intro i
    change internalLevel h i - 1 < internalLevel h i
    exact Nat.sub_lt (internalLevel_pos_le h i).1 (by omega)

end Ostmann.Arithmetic.HistorySymbolicScope

end

end OAI
