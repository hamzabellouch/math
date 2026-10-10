import OAI.NumberTheory.Ostmann.Construction.AssignmentReinsert

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
open Construction

def consLeftEquiv {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin (n + 1) ≃ Fin (a + 1) ⊕ Fin b where
  toFun := Fin.cases (.inl 0) (Sum.map Fin.succ id ∘ e)
  invFun := Sum.elim
    (Fin.cases 0 (fun i => (e.symm (.inl i)).succ))
    (fun i => (e.symm (.inr i)).succ)
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · cases hj : e j with
      | inl k =>
        have hk : e.symm (.inl k) = j := by rw [← hj, e.symm_apply_apply]
        simp [hj, hk]
      | inr k =>
        have hk : e.symm (.inr k) = j := by rw [← hj, e.symm_apply_apply]
        simp [hj, hk]
  right_inv := by
    intro i
    cases i with
    | inl j =>
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · simp
    | inr j => simp

@[simp] theorem consLeftEquiv_zero {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    consLeftEquiv e 0 = .inl 0 := rfl

@[simp] theorem consLeftEquiv_succ {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (i : Fin n) :
    consLeftEquiv e i.succ = Sum.map Fin.succ id (e i) := rfl

@[simp] theorem consLeftEquiv_symm_inl_zero {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    (consLeftEquiv e).symm (.inl 0) = 0 := rfl

@[simp] theorem consLeftEquiv_symm_inl_succ {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i : Fin a) :
    (consLeftEquiv e).symm (.inl i.succ) = (e.symm (.inl i)).succ := rfl

@[simp] theorem consLeftEquiv_symm_inr {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i : Fin b) :
    (consLeftEquiv e).symm (.inr i) = (e.symm (.inr i)).succ := rfl

def consRightEquiv {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin (n + 1) ≃ Fin a ⊕ Fin (b + 1) where
  toFun := Fin.cases (.inr 0) (Sum.map id Fin.succ ∘ e)
  invFun := Sum.elim
    (fun i => (e.symm (.inl i)).succ)
    (Fin.cases 0 (fun i => (e.symm (.inr i)).succ))
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · cases hj : e j with
      | inl k =>
        have hk : e.symm (.inl k) = j := by rw [← hj, e.symm_apply_apply]
        simp [hj, hk]
      | inr k =>
        have hk : e.symm (.inr k) = j := by rw [← hj, e.symm_apply_apply]
        simp [hj, hk]
  right_inv := by
    intro i
    cases i with
    | inl j => simp
    | inr j =>
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · simp

@[simp] theorem consRightEquiv_zero {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    consRightEquiv e 0 = .inr 0 := rfl

@[simp] theorem consRightEquiv_succ {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (i : Fin n) :
    consRightEquiv e i.succ = Sum.map id Fin.succ (e i) := rfl

@[simp] theorem consRightEquiv_symm_inl {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i : Fin a) :
    (consRightEquiv e).symm (.inl i) = (e.symm (.inl i)).succ := rfl

@[simp] theorem consRightEquiv_symm_inr_zero {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    (consRightEquiv e).symm (.inr 0) = 0 := rfl

@[simp] theorem consRightEquiv_symm_inr_succ {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i : Fin b) :
    (consRightEquiv e).symm (.inr i.succ) = (e.symm (.inr i)).succ := rfl

def splitPositions (j : ℕ) : (T : List SourceSlot) →
    Fin T.length ≃ Fin (Template.extracted j T).length ⊕ Fin (Template.remainder j T).length
  | [] => { toFun := Fin.elim0
            invFun := Sum.elim Fin.elim0 Fin.elim0
            left_inv := fun i => Fin.elim0 i
            right_inv := fun i => by rcases i with i | i <;> exact Fin.elim0 i }
  | q::T => if hq : q.role=.compensation j then
      (consLeftEquiv (splitPositions j T)).trans
        (Equiv.sumCongr (finCongr (by simp [Template.extracted,hq]))
          (finCongr (by simp [Template.remainder,hq])))
    else (consRightEquiv (splitPositions j T)).trans
      (Equiv.sumCongr (finCongr (by simp [Template.extracted,hq]))
        (finCongr (by simp [Template.remainder,hq])))

theorem splitPositions_getD (j : ℕ) (T : List SourceSlot) (i : Fin T.length) (d : SourceSlot) :
    T[i.val]?.getD d = Sum.elim
      (fun u => (Template.extracted j T)[u.val]?.getD d)
      (fun r => (Template.remainder j T)[r.val]?.getD d) (splitPositions j T i) := by
  induction T with
  | nil => exact Fin.elim0 i
  | cons q T ih =>
    by_cases hq : q.role=.compensation j
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp [splitPositions,hq,Template.extracted,Template.remainder]
        rfl
      · have ht := ih i
        cases hi : splitPositions j T i with
        | inl u =>
          rw [hi] at ht
          rw [splitPositions,dite_eq_left hq,Equiv.trans_apply]
          dsimp only [consLeftEquiv,Equiv.coe_fn_mk,Fin.cases_succ,Function.comp_apply]
          rw [hi]
          convert ht using 1 <;>
            simp [Template.extracted,Template.remainder,hq]
          change (Template.extracted j T)[u.val]?.getD d = (Template.extracted j T)[u.val]
          simp
        | inr r =>
          rw [hi] at ht
          rw [splitPositions,dite_eq_left hq,Equiv.trans_apply]
          dsimp only [consLeftEquiv,Equiv.coe_fn_mk,Fin.cases_succ,Function.comp_apply]
          rw [hi]
          convert ht using 1 <;>
            simp [Template.extracted,Template.remainder,hq]
          rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp [splitPositions,hq,Template.extracted,Template.remainder]
        rfl
      · have ht := ih i
        cases hi : splitPositions j T i with
        | inl u =>
          rw [hi] at ht
          rw [splitPositions,dite_eq_right hq,Equiv.trans_apply]
          dsimp only [consRightEquiv,Equiv.coe_fn_mk,Fin.cases_succ,Function.comp_apply]
          rw [hi]
          convert ht using 1 <;>
            simp [Template.extracted,Template.remainder,hq]
          change (Template.extracted j T)[u.val]?.getD d = (Template.extracted j T)[u.val]
          simp
        | inr r =>
          rw [hi] at ht
          rw [splitPositions,dite_eq_right hq,Equiv.trans_apply]
          dsimp only [consRightEquiv,Equiv.coe_fn_mk,Fin.cases_succ,Function.comp_apply]
          rw [hi]
          convert ht using 1 <;>
            simp [Template.extracted,Template.remainder,hq]
          rfl

lemma getD_fin {α : Type} (T : List α) (i : Fin T.length) (d : α) :
    T[i.val]?.getD d=T.get i := by
  simp [List.get_eq_getElem]

theorem splitPositions_slot (j : ℕ) (T : List SourceSlot) (i : Fin T.length) :
    T.get i = Sum.elim (Template.extracted j T).get (Template.remainder j T).get
      (splitPositions j T i) := by
  simpa only [getD_fin] using splitPositions_getD j T i ⟨.bulk,0⟩

end Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching

end

end OAI
