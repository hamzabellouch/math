import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicScope

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicNumerator
open Construction Characters.RationalHistory HistorySymbolicStep HistorySymbolicScope
open HistorySymbolicState HistoryOccurrenceVariables HistorySymbolicEncoding

variable {ι : Type*}

local instance keyDecidableEq {l : ℕ} (h : History l) : DecidableEq (Key h) := Classical.decEq _

def numeratorExpr (v w : ℤ) (plus minus : Expr ι) (hp hm : List (Expr ι)) : Expr ι :=
  .sub (.mul (.fixed v) (.mul minus (product hm)))
    (.mul (.fixed w) (.mul plus (product hp)))

theorem product_denominator_one (es : List (Expr ι))
    (h : ∀ e ∈ es, e.denominator = 1) : (product es).denominator = 1 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      change e.denominator * (product es).denominator = 1
      rw [h e (by simp),ih (fun z hz => h z (by simp [hz])),one_mul]

theorem pivot_numerator_eq (s v w : ℤ) (plus minus : Expr ι) (u hp hm : List (Expr ι))
    (hu : ∀ e ∈ u, e.denominator = 1) :
    (pivot s v w plus minus u hp hm).numerator =
      (numeratorExpr v w plus minus hp hm).numerator := by
  change (numeratorExpr v w plus minus hp hm).numerator *
      (1 * (product u).denominator) = _
  rw [product_denominator_one u hu,mul_one,mul_one]

theorem numeratorExpr_above (v w : ℤ) (plus minus : Expr ι) (hp hm : List (Expr ι))
    (level : ι → ℕ) (t : ℕ) (hplus : Above level t plus) (hminus : Above level t minus)
    (hhp : ∀ e ∈ hp, Above level t e) (hhm : ∀ e ∈ hm, Above level t e) :
    Above level t (numeratorExpr v w plus minus hp hm) :=
  ⟨⟨trivial,hminus,product_above hm hhm⟩,⟨trivial,hplus,product_above hp hhp⟩⟩

theorem pivot_numerator_vars_above [DecidableEq ι]
    (s v w : ℤ) (plus minus : Expr ι) (u hp hm : List (Expr ι))
    (level : ι → ℕ) (t : ℕ) (hplus : Above level t plus) (hminus : Above level t minus)
    (hhp : ∀ e ∈ hp, Above level t e) (hhm : ∀ e ∈ hm, Above level t e)
    (hu : ∀ e ∈ u, e.denominator = 1) :
    ∀ i ∈ (pivot s v w plus minus u hp hm).numerator.vars, t < level i := by
  rw [pivot_numerator_eq s v w plus minus u hp hm hu]
  intro i hi
  exact above_atoms _ (numeratorExpr_above v w plus minus hp hm level t hplus hminus hhp hhm)
    i ((numeratorExpr v w plus minus hp hm).fraction_vars_subset.1 hi)

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem pivotExpr_vars_above [DecidableEq ι]
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (level : ι → ℕ)
    (he : StateAbove level (l+1) e) (hc : ∀ i, (comp i).denominator = 1) :
    ∀ i ∈ (pivotExpr hs e comp).numerator.vars, l+1 < level i := by
  apply pivot_numerator_vars_above
  · exact he.1
  · exact he.2.1
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact he.2.2 _
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact he.2.2 _
  · intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact hc i

def rootState : {l : ℕ} → (h : History l) → TreeExpr ι h → StateExpr h.root ι
  | _, .leaf _, e => e
  | _, .node _ _ _ _ _ _ _, e => e.1

def TreeNumeratorsAbove [DecidableEq ι] (level : ι → ℕ) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, _ => True
  | l+1, .node _ _ _ _ _ left right, e =>
      (∀ i ∈ (rootState left e.2.1).plus.numerator.vars, l+1 < level i) ∧
      TreeNumeratorsAbove level left e.2.1 ∧ TreeNumeratorsAbove level right e.2.2

@[simp] theorem rootState_encode {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) : rootState h (encode V outside h hs e comp) = e := by
  cases h <;> rfl

theorem encode_numerators_above [DecidableEq ι]
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (level : ι → ℕ)
    (e : StateExpr h.root ι) (comp : InternalKey h → Expr ι)
    (he : StateAbove level l e)
    (hc : ∀ i, Above level (internalLevel h i - 1) (comp i))
    (hd : ∀ i, (comp i).denominator = 1) :
    TreeNumeratorsAbove level h (encode V outside h hs e comp) := by
  induction h with
  | leaf a => trivial
  | @node l a p u hp hm left right ihl ihr =>
      have hu : ∀ i, Above level l (comp (Sum.inl i)) := by
        intro i
        simpa only [internalLevel,Sum.elim_inl,Nat.add_sub_cancel] using hc (Sum.inl i)
      have hchildren := child_above hs level e _ he hu
      refine ⟨?_,?_,?_⟩
      · simp only [encode,rootState_encode,leftState]
        exact pivotExpr_vars_above hs e _ level he (fun i => hd (Sum.inl i))
      · exact ihl (History.supported_left hs) _ _ hchildren.1
          (fun i => hc (Sum.inr (Sum.inl i))) (fun i => hd (Sum.inr (Sum.inl i)))
      · exact ihr (History.supported_right hs) _ _ hchildren.2
          (fun i => hc (Sum.inr (Sum.inr i))) (fun i => hd (Sum.inr (Sum.inr i)))

theorem symbolicHistory_numerators_above {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    TreeNumeratorsAbove (keyLevel h) h (symbolicHistory h hs) := by
  classical
  apply encode_numerators_above
  · exact ⟨Nat.lt_succ_self l,Nat.lt_succ_self l,fun _ => Nat.lt_succ_self l⟩
  · intro i
    change internalLevel h i - 1 < internalLevel h i
    exact Nat.sub_lt (internalLevel_pos_le h i).1 (by omega)
  · intro i
    rfl

end Ostmann.Arithmetic.HistorySymbolicNumerator

end

end OAI
