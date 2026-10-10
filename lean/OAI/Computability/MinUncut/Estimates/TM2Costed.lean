import Mathlib
import OAI.Computability.MinUncut.Estimates.CodeComputability

namespace OAI

section
namespace MinUncut.Costed

open Function

def Steps {α : Type*} (f : α → Option α) (n : ℕ) (a b : α) : Prop :=
  (fun x : Option α => x.bind f)^[n] (some a) = some b

@[simp] theorem steps_zero {α : Type*} (f : α → Option α) (a b : α) :
    Steps f 0 a b ↔ a = b := by
  simp [Steps]

theorem steps_one {α : Type*} {f : α → Option α} {a b : α}
    (h : f a = some b) : Steps f 1 a b := h

theorem steps_head {α : Type*} {f : α → Option α} {n : ℕ} {a b c : α}
    (h : f a = some b) (h' : Steps f n b c) : Steps f (n + 1) a c := by
  simpa only [Steps, Function.iterate_succ_apply, Option.bind_some, h] using h'

theorem steps_trans {α : Type*} {f : α → Option α} {m n : ℕ} {a b c : α}
    (h : Steps f m a b) (h' : Steps f n b c) : Steps f (m + n) a c := by
  dsimp [Steps] at *
  rw [Nat.add_comm m n, Function.iterate_add_apply, h, h']

def steps_timed {α : Type*} {f : α → Option α} {n m : ℕ} {a b : α}
    (h : Steps f n a b) (hn : n ≤ m) : StateTransition.EvalsToInTime f a (some b) m :=
  ⟨⟨n, h⟩, hn⟩

def Within {α : Type*} (f : α → Option α) (n : ℕ) (a b : α) : Prop :=
  ∃ t, t ≤ n ∧ Steps f t a b

theorem Steps.within {α : Type*} {f : α → Option α} {n : ℕ} {a b : α}
    (h : Steps f n a b) : Within f n a b := ⟨n, le_rfl, h⟩

theorem Within.mono {α : Type*} {f : α → Option α} {m n : ℕ} {a b : α}
    (h : Within f m a b) (hmn : m ≤ n) : Within f n a b := by
  obtain ⟨t, ht, he⟩ := h
  exact ⟨t, ht.trans hmn, he⟩

theorem Within.trans {α : Type*} {f : α → Option α} {m n : ℕ} {a b c : α}
    (h : Within f m a b) (h' : Within f n b c) : Within f (m + n) a c := by
  obtain ⟨t, ht, he⟩ := h
  obtain ⟨t', ht', he'⟩ := h'
  exact ⟨t+t', Nat.add_le_add ht ht', steps_trans he he'⟩

theorem Within.head {α : Type*} {f : α → Option α} {n : ℕ} {a b c : α}
    (h : f a = some b) (h' : Within f n b c) : Within f (n + 1) a c := by
  obtain ⟨t, ht, he⟩ := h'
  exact ⟨t+1, Nat.add_le_add_right ht 1, steps_head h he⟩

theorem within_one {α : Type*} {f : α → Option α} {a b : α}
    (h : f a = some b) : Within f 1 a b := (steps_one h).within

end MinUncut.Costed

namespace Turing.PartrecToTM2
open scoped _root_.Turing _root_.Turing.PartrecToTM2
open Function
open MinUncut.Costed
open _root_.Turing.PartrecToTM2.K'

theorem move_steps {p k₁ k₂ q s L₁ o L₂} {S : _root_.Turing.PartrecToTM2.K' → List _root_.Turing.PartrecToTM2.Γ'} (h₁ : k₁ ≠ k₂)
    (e : _root_.Turing.PartrecToTM2.splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (L₁.length + 1) ⟨some (_root_.Turing.PartrecToTM2.Λ'.move p k₁ k₂ q), s, S⟩
      ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverseAux (S k₂))⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    rw [(_ : [].reverseAux _ = _), Function.update_eq_self]
    swap
    · rw [Function.update_of_ne h₁.symm, List.reverseAux_nil]
    apply steps_one
    simp only [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.tr_move, _root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux, Option.elim]
    grind [_root_.Turing.PartrecToTM2.splitAtPred.eq_def]
  | cons a L₁ IH =>
    refine steps_head rfl ?_
    rw [_root_.Turing.PartrecToTM2.tr]; simp only [_root_.Turing.PartrecToTM2.pop', Option.elim, _root_.Turing.TM2.stepAux, _root_.Turing.PartrecToTM2.push']
    rcases e₁ : S k₁ with - | ⟨a', Sk⟩ <;> rw [e₁, _root_.Turing.PartrecToTM2.splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : _root_.Turing.PartrecToTM2.splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, Bool.cond_false]
    convert! @IH _ (update (update S k₁ Sk) k₂ (a :: S k₂)) _ using 2 <;>
      simp [Function.update_of_ne, h₁, h₁.symm, e₃, List.reverseAux]
    simp [Function.update_comm h₁.symm]

theorem clear_steps {p k q s L₁ o L₂} {S : _root_.Turing.PartrecToTM2.K' → List _root_.Turing.PartrecToTM2.Γ'}
    (e : _root_.Turing.PartrecToTM2.splitAtPred p (S k) = (L₁, o, L₂)) :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (L₁.length + 1) ⟨some (_root_.Turing.PartrecToTM2.Λ'.clear p k q), s, S⟩
      ⟨some q, o, update S k L₂⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    apply steps_one
    simp only [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.tr_clear, _root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux]
    grind [_root_.Turing.PartrecToTM2.splitAtPred.eq_def]
  | cons a L₁ IH =>
    refine steps_head rfl ?_
    rw [_root_.Turing.PartrecToTM2.tr]; simp only [_root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux, Option.elim]
    rcases e₁ : S k with - | ⟨a', Sk⟩ <;> rw [e₁, _root_.Turing.PartrecToTM2.splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : _root_.Turing.PartrecToTM2.splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, Bool.cond_false]
    convert! @IH _ (update S k Sk) _ using 2 <;> simp [e₃]

theorem unrev_steps {q s} {S : _root_.Turing.PartrecToTM2.K' → List _root_.Turing.PartrecToTM2.Γ'} :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) ((S rev).length + 1) ⟨some (_root_.Turing.PartrecToTM2.unrev q), s, S⟩
      ⟨some q, none, update (update S rev []) main (List.reverseAux (S rev) (S main))⟩ :=
  move_steps (by decide) (_root_.Turing.PartrecToTM2.splitAtPred_false _)

theorem copy_steps (q s a b c d) :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (b.length + 1) ⟨some (_root_.Turing.PartrecToTM2.Λ'.copy q), s, _root_.Turing.PartrecToTM2.K'.elim a b c d⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (List.reverseAux b a) [] c (List.reverseAux b d)⟩ := by
  induction b generalizing a d s with
  | nil =>
    apply steps_one
    simp [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.tr, _root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux]
  | cons x b IH =>
    refine steps_head rfl ?_
    rw [_root_.Turing.PartrecToTM2.tr]
    simp only [_root_.Turing.TM2.stepAux, elim_rev, List.head?_cons, Option.isSome_some,
      List.tail_cons, elim_update_rev, elim_main, elim_update_main,
      elim_stack, elim_update_stack, Bool.cond_true, List.reverseAux_cons, _root_.Turing.PartrecToTM2.pop', _root_.Turing.PartrecToTM2.push']
    exact IH _ _ _

theorem move₂_steps {p k₁ k₂ q s L₁ o L₂} {S : _root_.Turing.PartrecToTM2.K' → List _root_.Turing.PartrecToTM2.Γ'}
    (h₁ : k₁ ≠ rev ∧ k₂ ≠ rev ∧ k₁ ≠ k₂) (h₂ : S rev = [])
    (e : _root_.Turing.PartrecToTM2.splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2 * L₁.length + 3) ⟨some (_root_.Turing.PartrecToTM2.move₂ p k₁ k₂ q), s, S⟩
      ⟨some q, none, update (update S k₁ (o.elim id List.cons L₂)) k₂ (L₁ ++ S k₂)⟩ := by
  have heq : 2 * L₁.length + 3 = (L₁.length + 1) + ((L₁.length + 1) + 1) := by omega
  rw [heq]
  refine steps_trans (move_steps h₁.1 e) (steps_head rfl ?_)
  cases o <;> rw [_root_.Turing.PartrecToTM2.tr]
    <;> simp only [id, _root_.Turing.TM2.stepAux, Option.isSome, Bool.cond_true, Bool.cond_false, Option.elim]
  · convert! move_steps h₁.2.1.symm (_root_.Turing.PartrecToTM2.splitAtPred_false _) using 2
    · simp [Function.update_self, List.reverseAux_eq, h₂]
    simp only [Function.update_comm h₁.1, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.2.2.symm, Function.update_of_ne h₁.2.1,
      Function.update_of_ne h₁.1.symm, List.reverseAux_eq, h₂, Function.update_self,
      List.append_nil, List.reverse_reverse]
  · simp only [Option.getD_some]
    convert! move_steps h₁.2.1.symm (_root_.Turing.PartrecToTM2.splitAtPred_false _) using 2
    · simp [Function.update_self, Function.update_of_ne h₁.1.symm, List.reverseAux_eq, h₂]
    simp only [h₂, Function.update_comm h₁.1, List.reverseAux_eq, Function.update_self,
      List.append_nil, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.1.symm, Function.update_of_ne h₁.2.2.symm,
      Function.update_of_ne h₁.2.1, Function.update_self, List.reverse_reverse]

theorem head_main_steps {q s L} {c d : List _root_.Turing.PartrecToTM2.Γ'} :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2*(_root_.Turing.PartrecToTM2.trNat L.headI).length+(_root_.Turing.PartrecToTM2.trList L.tail).length+6)
      ⟨some (_root_.Turing.PartrecToTM2.head main q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L) [] c d⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList [L.headI]) [] c d⟩ := by
  let o : Option _root_.Turing.PartrecToTM2.Γ' := List.casesOn L none fun _ _ => some _root_.Turing.PartrecToTM2.Γ'.cons
  have heq : 2*(_root_.Turing.PartrecToTM2.trNat L.headI).length+(_root_.Turing.PartrecToTM2.trList L.tail).length+6 =
      ((_root_.Turing.PartrecToTM2.trNat L.headI).length+1) +
        ((((_root_.Turing.PartrecToTM2.trList L.tail).length+1)+((_root_.Turing.PartrecToTM2.trNat L.headI).length+2)+1)+1) := by omega
  rw [heq]
  refine steps_trans
    (move_steps (by decide)
      (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ (_root_.Turing.PartrecToTM2.trNat L.headI) o (_root_.Turing.PartrecToTM2.trList L.tail) (_root_.Turing.PartrecToTM2.trNat_natEnd _) ?_))
      (steps_head rfl (steps_head rfl ?_))
  · cases L <;> simp [o]
  rw [_root_.Turing.PartrecToTM2.tr]
  simp only [_root_.Turing.TM2.stepAux, elim_update_main, elim_rev, elim_update_rev,
    Function.update_self, _root_.Turing.PartrecToTM2.trList]
  rw [ite_eq_right (show o ≠ some _root_.Turing.PartrecToTM2.Γ'.consₗ by cases L <;> simp [o])]
  refine steps_trans (clear_steps (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ _ none [] ?_ ⟨rfl,rfl⟩)) ?_
  · exact fun x h => Bool.decide_false (_root_.Turing.PartrecToTM2.trList_ne_consₗ _ _ h)
  simpa [List.reverseAux_eq] using
    (unrev_steps (q := q) (s := none) (S := _root_.Turing.PartrecToTM2.K'.elim [] (_root_.Turing.PartrecToTM2.Γ'.cons :: (_root_.Turing.PartrecToTM2.trNat L.headI).reverse) c d))

theorem head_stack_time {q s L₁ L₂ L₃} :
    Within (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2*(_root_.Turing.PartrecToTM2.trList L₂).length+6)
      ⟨some (_root_.Turing.PartrecToTM2.head stack q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L₁) [] [] (_root_.Turing.PartrecToTM2.trList L₂ ++ _root_.Turing.PartrecToTM2.Γ'.consₗ :: L₃)⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList (L₂.headI :: L₁)) [] [] L₃⟩ := by
  rcases L₂ with - | ⟨a, L₂⟩
  · have h : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (1+(2+1+1))
        ⟨some (_root_.Turing.PartrecToTM2.head stack q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L₁) [] [] (_root_.Turing.PartrecToTM2.trList [] ++ _root_.Turing.PartrecToTM2.Γ'.consₗ :: L₃)⟩
        ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList ([].headI :: L₁)) [] [] L₃⟩ := by
      refine steps_trans
        (move_steps (by decide)
          (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ [] (some _root_.Turing.PartrecToTM2.Γ'.consₗ) L₃ (by rintro _ ⟨⟩) ⟨rfl,rfl⟩))
        (steps_head rfl (steps_head rfl ?_))
      rw [_root_.Turing.PartrecToTM2.tr]
      simp only [_root_.Turing.TM2.stepAux, ite_true, id_eq, _root_.Turing.PartrecToTM2.trList, List.nil_append,
        elim_update_stack, elim_rev, List.reverseAux_nil, elim_update_rev,
        Function.update_self, List.headI_nil, _root_.Turing.PartrecToTM2.trNat_default]
      convert! unrev_steps using 2 <;> simp
    exact h.within.mono (by simp)
  · have h : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr)
        (((_root_.Turing.PartrecToTM2.trNat a).length+1)+((((_root_.Turing.PartrecToTM2.trList L₂).length+1)+((_root_.Turing.PartrecToTM2.trNat a).length+2)+1)+1))
        ⟨some (_root_.Turing.PartrecToTM2.head stack q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L₁) [] [] (_root_.Turing.PartrecToTM2.trList (a::L₂) ++ _root_.Turing.PartrecToTM2.Γ'.consₗ :: L₃)⟩
        ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList ((a::L₂).headI :: L₁)) [] [] L₃⟩ := by
      refine steps_trans
        (move_steps (by decide)
          (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ (_root_.Turing.PartrecToTM2.trNat a) (some _root_.Turing.PartrecToTM2.Γ'.cons) (_root_.Turing.PartrecToTM2.trList L₂ ++ _root_.Turing.PartrecToTM2.Γ'.consₗ :: L₃)
            (_root_.Turing.PartrecToTM2.trNat_natEnd _) ⟨rfl, by simp⟩))
        (steps_head rfl (steps_head rfl ?_))
      simp only [_root_.Turing.PartrecToTM2.trList, List.append_assoc,
        List.cons_append, elim_update_stack, elim_rev, elim_update_rev,
        Function.update_self, List.headI_cons]
      refine steps_trans
        (clear_steps
          (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ (_root_.Turing.PartrecToTM2.trList L₂) (some _root_.Turing.PartrecToTM2.Γ'.consₗ) L₃
            (fun x h => Bool.decide_false (_root_.Turing.PartrecToTM2.trList_ne_consₗ _ _ h)) ⟨rfl, by simp⟩)) ?_
      simpa [List.reverseAux_eq] using
        (unrev_steps (q := q) (s := some _root_.Turing.PartrecToTM2.Γ'.consₗ) (S := _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L₁) (_root_.Turing.PartrecToTM2.Γ'.cons :: (_root_.Turing.PartrecToTM2.trNat a).reverse) [] L₃))
    exact h.within.mono (by simp only [_root_.Turing.PartrecToTM2.trList, List.length_append, List.length_cons]; omega)

theorem succ_time {q s n} {c d : List _root_.Turing.PartrecToTM2.Γ'} :
    Within (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2*(_root_.Turing.PartrecToTM2.trNat n).length+2)
      ⟨some (_root_.Turing.PartrecToTM2.Λ'.succ q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList [n]) [] c d⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList [n.succ]) [] c d⟩ := by
  simp only [_root_.Turing.PartrecToTM2.trList, _root_.Turing.PartrecToTM2.trNat.eq_1, Nat.cast_succ, Num.add_one]
  rcases (n : Num) with - | a
  · have h : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (1+1)
        ⟨some (_root_.Turing.PartrecToTM2.Λ'.succ q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trNum Num.zero ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList []) [] c d⟩
        ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trNum (Num.succ Num.zero) ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList []) [] c d⟩ := by
      refine steps_head rfl ?_
      convert! (unrev_steps (q := q) (s := some _root_.Turing.PartrecToTM2.Γ'.cons) (S := _root_.Turing.PartrecToTM2.K'.elim [_root_.Turing.PartrecToTM2.Γ'.bit1, _root_.Turing.PartrecToTM2.Γ'.cons] [] c d)) using 1 <;> simp <;> rfl
    exact h.within
  simp only [_root_.Turing.PartrecToTM2.trNum, Num.succ, Num.succ']
  have hpref : ∀ l₁, ∃ l₁' l₂' s' t,
      List.reverseAux l₁ (_root_.Turing.PartrecToTM2.trPosNum a.succ) = List.reverseAux l₁' l₂' ∧
      Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) t ⟨some q.succ, s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trPosNum a ++ [_root_.Turing.PartrecToTM2.Γ'.cons]) l₁ c d⟩
        ⟨some (_root_.Turing.PartrecToTM2.unrev q), s', _root_.Turing.PartrecToTM2.K'.elim (l₂' ++ [_root_.Turing.PartrecToTM2.Γ'.cons]) l₁' c d⟩ ∧
      t ≤ (_root_.Turing.PartrecToTM2.trPosNum a).length+1 ∧ l₁'.length ≤ l₁.length+(_root_.Turing.PartrecToTM2.trPosNum a).length := by
    induction a generalizing s with intro l₁
    | one =>
      refine ⟨_root_.Turing.PartrecToTM2.Γ'.bit0::l₁, [_root_.Turing.PartrecToTM2.Γ'.bit1], some _root_.Turing.PartrecToTM2.Γ'.cons, 2, rfl,
        steps_head rfl (steps_one ?_), by simp [_root_.Turing.PartrecToTM2.trPosNum], by simp [_root_.Turing.PartrecToTM2.trPosNum]⟩
      simp [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.trPosNum]
    | bit1 m IH =>
      obtain ⟨l₁',l₂',s',t,e,h,ht,hl⟩ := IH (_root_.Turing.PartrecToTM2.Γ'.bit0::l₁)
      refine ⟨l₁',l₂',s',t+1,e,steps_head ?_ h,?_,?_⟩
      · simp [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.trPosNum]
        rfl
      · simp only [_root_.Turing.PartrecToTM2.trPosNum,List.length_cons]; omega
      · simp only [_root_.Turing.PartrecToTM2.trPosNum,List.length_cons] at *; omega
    | bit0 m _ =>
      refine ⟨l₁, _, some _root_.Turing.PartrecToTM2.Γ'.bit0, 1, rfl, steps_one ?_, by simp [_root_.Turing.PartrecToTM2.trPosNum], by simp [_root_.Turing.PartrecToTM2.trPosNum]⟩
      simp only [_root_.Turing.TM2.step]; rw [_root_.Turing.PartrecToTM2.tr]
      simp only [_root_.Turing.TM2.stepAux, _root_.Turing.PartrecToTM2.pop', elim_main, elim_update_main,
        elim_rev, elim_update_rev, Function.update_self]
      rfl
  obtain ⟨l₁',l₂',s',t,e,h,ht,hl⟩ := hpref []
  simp only [List.reverseAux_nil] at e
  have hu : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (l₁'.length+1)
      ⟨some (_root_.Turing.PartrecToTM2.unrev q), s', _root_.Turing.PartrecToTM2.K'.elim (l₂' ++ [_root_.Turing.PartrecToTM2.Γ'.cons]) l₁' c d⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trPosNum a.succ ++ [_root_.Turing.PartrecToTM2.Γ'.cons]) [] c d⟩ := by
    convert! unrev_steps using 2 <;> simp [e,List.reverseAux_eq]
  exact (steps_trans h hu).within.mono (by simp only [List.length_nil, zero_add] at hl; omega)

theorem pred_time (q₁ q₂ s v) (c d : List _root_.Turing.PartrecToTM2.Γ') : ∃ s',
    Within (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2*(_root_.Turing.PartrecToTM2.trList v).length+3)
      ⟨some (_root_.Turing.PartrecToTM2.Λ'.pred q₁ q₂), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList v) [] c d⟩
      (v.headI.rec ⟨some q₁, s', _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList v.tail) [] c d⟩ fun n _ =>
        ⟨some q₂, s', _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList (n::v.tail)) [] c d⟩) := by
  rcases v with (_ | ⟨_ | n, v⟩)
  · refine ⟨none, (within_one ?_).mono (by simp)⟩
    simp [_root_.Turing.TM2.step]
  · refine ⟨some _root_.Turing.PartrecToTM2.Γ'.cons, (within_one ?_).mono (by simp)⟩
    simp [_root_.Turing.TM2.step]
  refine ⟨none, ?_⟩
  simp only [_root_.Turing.PartrecToTM2.trList, _root_.Turing.PartrecToTM2.trNat.eq_1, _root_.Turing.PartrecToTM2.trNum, Nat.cast_succ, Num.add_one, Num.succ,
    List.tail_cons, List.headI_cons]
  rcases (n : Num) with - | a
  · simp only [_root_.Turing.PartrecToTM2.trPosNum, Num.succ', List.singleton_append, List.nil_append]
    have h : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (1+1)
        ⟨some (_root_.Turing.PartrecToTM2.Λ'.pred q₁ q₂), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.Γ'.bit1::_root_.Turing.PartrecToTM2.Γ'.cons::_root_.Turing.PartrecToTM2.trList v) [] c d⟩
        ⟨some q₂, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.Γ'.cons::_root_.Turing.PartrecToTM2.trList v) [] c d⟩ := by
      refine steps_head rfl ?_
      rw [_root_.Turing.PartrecToTM2.tr]; simp only [_root_.Turing.PartrecToTM2.pop', _root_.Turing.TM2.stepAux]
      convert! unrev_steps using 2 <;> simp
    exact h.within.mono (by simp)
  simp only [Num.succ']
  have hpref : ∀ l₁, ∃ l₁' l₂' s' t,
      List.reverseAux l₁ (_root_.Turing.PartrecToTM2.trPosNum a) = List.reverseAux l₁' l₂' ∧
      Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) t
        ⟨some (q₁.pred q₂), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trPosNum a.succ ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList v) l₁ c d⟩
        ⟨some (_root_.Turing.PartrecToTM2.unrev q₂), s', _root_.Turing.PartrecToTM2.K'.elim (l₂' ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList v) l₁' c d⟩ ∧
      t ≤ (_root_.Turing.PartrecToTM2.trPosNum a.succ).length+1 ∧ l₁'.length ≤ l₁.length+(_root_.Turing.PartrecToTM2.trPosNum a.succ).length := by
    induction a generalizing s with intro l₁
    | one =>
      refine ⟨_root_.Turing.PartrecToTM2.Γ'.bit1::l₁, [], some _root_.Turing.PartrecToTM2.Γ'.cons, 2, rfl,
        steps_head rfl (steps_one ?_), by simp [_root_.Turing.PartrecToTM2.trPosNum,PosNum.succ], by simp [_root_.Turing.PartrecToTM2.trPosNum,PosNum.succ]⟩
      simp [_root_.Turing.TM2.step, _root_.Turing.PartrecToTM2.trPosNum, show PosNum.one.succ = PosNum.one.bit0 from rfl]
    | bit1 m IH =>
      obtain ⟨l₁',l₂',s',t,e,h,ht,hl⟩ := IH (some _root_.Turing.PartrecToTM2.Γ'.bit0) (_root_.Turing.PartrecToTM2.Γ'.bit1::l₁)
      refine ⟨l₁',l₂',s',t+1,e,steps_head ?_ h,?_,?_⟩
      · simp [_root_.Turing.TM2.step]
        rfl
      · simp only [PosNum.succ,_root_.Turing.PartrecToTM2.trPosNum,List.length_cons]; omega
      · simp only [PosNum.succ,_root_.Turing.PartrecToTM2.trPosNum,List.length_cons] at *; omega
    | bit0 m _ =>
      obtain ⟨a,l,e,h⟩ : ∃ a l, _root_.Turing.PartrecToTM2.trPosNum m=a::l ∧ _root_.Turing.PartrecToTM2.natEnd a=false := by
        cases m <;> refine ⟨_,_,rfl,rfl⟩
      refine ⟨_root_.Turing.PartrecToTM2.Γ'.bit0::l₁, _, some a, 1, rfl, steps_one ?_,
        by simp [PosNum.succ,_root_.Turing.PartrecToTM2.trPosNum], by simp [PosNum.succ,_root_.Turing.PartrecToTM2.trPosNum]⟩
      simp [_root_.Turing.TM2.step,_root_.Turing.PartrecToTM2.trPosNum,PosNum.succ,e,h,show some _root_.Turing.PartrecToTM2.Γ'.bit1 ≠ some _root_.Turing.PartrecToTM2.Γ'.bit0 by decide,
        Option.getD,-_root_.Turing.PartrecToTM2.natEnd]
      simp [_root_.Turing.PartrecToTM2.natEnd]
  obtain ⟨l₁',l₂',s',t,e,h,ht,hl⟩ := hpref []
  simp only [List.reverseAux_nil] at e
  have hu : Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (l₁'.length+1)
      ⟨some (_root_.Turing.PartrecToTM2.unrev q₂), s', _root_.Turing.PartrecToTM2.K'.elim (l₂' ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList v) l₁' c d⟩
      ⟨some q₂, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trPosNum a ++ _root_.Turing.PartrecToTM2.Γ'.cons :: _root_.Turing.PartrecToTM2.trList v) [] c d⟩ := by
    convert! unrev_steps using 2 <;> simp [e,List.reverseAux_eq]
  exact (steps_trans h hu).within.mono (by
    simp only [List.length_nil,zero_add] at hl
    simp only [List.length_append,List.length_cons]; omega)

end Turing.PartrecToTM2

end

namespace MinUncut.Costed.WordTransducer
open _root_.Turing Function

inductive Tape | input | work | output deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .work, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def Alphabet (A B : Type) : Tape → Type
  | .input => A
  | .work | .output => B

def tapes {A B : Type} (input : List A) (work output : List B) :
    ∀ k,List (Alphabet A B k)
  | .input => input
  | .work => work
  | .output => output

@[simp] lemma update_input {A B : Type} (i i' : List A) (w o : List B) :
    update (tapes i w o) .input i'=tapes i' w o := by
  funext k
  cases k <;> simp only [tapes] <;> rfl
@[simp] lemma update_work {A B : Type} (i : List A) (w w' o : List B) :
    update (tapes i w o) .work w'=tapes i w' o := by
  funext k; cases k <;> rfl
@[simp] lemma update_output {A B : Type} (i : List A) (w o o' : List B) :
    update (tapes i w o) .output o'=tapes i w o' := by
  funext k; cases k <;> rfl

def pushWord {K Λ σ : Type} {Γ : K → Type} (dst : K) :
    List (Γ dst) → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], q => q
  | a::w, q => .push dst (fun _ => a) (pushWord dst w q)

lemma pushWord_aux {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] (dst : K)
    (w : List (Γ dst)) (q : TM2.Stmt Γ Λ σ) (s : σ) (st : ∀ k,List (Γ k)) :
    TM2.stepAux (pushWord dst w q) s st=
      TM2.stepAux q s (update st dst (w.reverse++st dst)) := by
  induction w generalizing st with
  | nil => simp [pushWord]
  | cons a w ih =>
    simp only [pushWord,TM2.stepAux,ih,update_self,update_idem,
      List.reverse_cons,List.append_assoc,List.singleton_append]

variable {A B Q : Type}
inductive Label (Q A : Type) | read | emit (q : Q) (a : A) | reverse
  deriving DecidableEq, Fintype
abbrev State (Q A B : Type) := Q × Option A × Option B

def output (next : Q → A → Q) (emit : Q → A → List B) : Q → List A → List B
  | _, [] => []
  | q,a::v => emit q a ++ output next emit (next q a) v

def program [Inhabited A] [Inhabited B] (initial : Q)
    (next : Q → A → Q) (emit : Q → A → List B) :
    Label Q A → TM2.Stmt (Alphabet A B) (Label Q A) (State Q A B)
  | .read => .pop .input (fun s a => (s.1,a,s.2.2))
      (.branch (fun s => s.2.1.isSome)
        (.goto fun s => .emit s.1 (s.2.1.getD default))
        (.load (fun _ => (initial,none,none)) (.goto fun _ => .reverse)))
  | .emit q a => .load (fun _ => (next q a,none,none))
      (pushWord .work (emit q a) (.goto fun _ => .read))
  | .reverse => .pop .work (fun s b => (s.1,s.2.1,b))
      (.branch (fun s => s.2.2.isSome)
        (.push .output (fun s => s.2.2.getD default) (.goto fun _ => .reverse))
        (.load (fun _ => (initial,none,none)) .halt))

def machine [Fintype A] [Fintype B] [Fintype Q] [Inhabited A] [Inhabited B]
    (initial : Q) (next : Q → A → Q) (emit : Q → A → List B) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A B
  Γk₀Fin := inferInstanceAs (Fintype A)
  Λ := Label Q A
  main := .read
  σ := State Q A B
  initialState := (initial,none,none)
  m := program initial next emit

lemma finiteAlphabet [Fintype A] [Fintype B] [Fintype Q] [Inhabited A] [Inhabited B]
    (initial : Q) (next : Q → A → Q) (emit : Q → A → List B)
    (k : (machine initial next emit).K) : Finite ((machine initial next emit).Γ k) := by
  cases k <;> dsimp [machine,Alphabet] <;> infer_instance

variable [Inhabited A] [Inhabited B]

lemma reverse_steps (initial : Q) (next : Q → A → Q) (emit : Q → A → List B)
    (w o : List B) (s : State Q A B) :
    Steps (TM2.step (program initial next emit)) (w.length+1)
      ⟨some .reverse,s,tapes [] w o⟩
      ⟨none,(initial,none,none),tapes [] [] (w.reverse++o)⟩ := by
  induction w generalizing s o with
  | nil =>
    apply steps_one
    simp only [TM2.step, program]
    exact congrArg (fun st => (some ⟨none, (initial, none, none), st⟩ :
      Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B))))
      (update_work (A := A) [] [] [] o)
  | cons b w ih =>
    have h : TM2.step (program initial next emit)
        ⟨some .reverse,s,tapes [] (b::w) o⟩=
        some ⟨some .reverse,(s.1,s.2.1,some b),tapes [] w (b::o)⟩ := by
      have hwork := update_work (A := A) [] (b :: w) w o
      have hout := update_output (A := A) [] w o (b :: o)
      have ht := (congrArg (fun st => update st Tape.output (b :: o)) hwork).trans hout
      exact congrArg (fun st => (some ⟨some .reverse, (s.1, s.2.1, some b), st⟩ :
        Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B)))) ht
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
      using steps_head h (ih (b::o) (s.1,s.2.1,some b))

lemma emit_steps (initial q : Q) (next : Q → A → Q) (emit : Q → A → List B)
    (a : A) (v : List A) (w : List B) :
    Steps (TM2.step (program initial next emit)) 2
      ⟨some .read,(q,none,none),tapes (a::v) w []⟩
      ⟨some .read,(next q a,none,none),tapes v ((emit q a).reverse++w) []⟩ := by
  apply steps_head (b := ⟨some (.emit q a),(q,some a,none),tapes v w []⟩)
  · exact congrArg (fun st => (some ⟨some (.emit q a), (q, some a, none), st⟩ :
      Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B))))
      (update_input (a :: v) v w [])
  · apply steps_one
    have hp := pushWord_aux (Γ := Alphabet A B) (Λ := Label Q A) (σ := State Q A B)
      Tape.work (emit q a) (.goto fun _ => .read) (next q a, none, none) (tapes v w [])
    exact (congrArg some hp).trans
      (congrArg (fun st => (some ⟨some .read, (next q a, none, none), st⟩ :
        Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B))))
        (update_work v w ((emit q a).reverse ++ w) []))

lemma read_steps (initial q : Q) (next : Q → A → Q) (emit : Q → A → List B)
    (v : List A) (w : List B) :
    Steps (TM2.step (program initial next emit)) (2*v.length+1)
      ⟨some .read,(q,none,none),tapes v w []⟩
      ⟨some .reverse,(initial,none,none),tapes [] ((output next emit q v).reverse++w) []⟩ := by
  induction v generalizing q w with
  | nil =>
    apply steps_one
    exact congrArg (fun st => (some ⟨some .reverse, (initial, none, none), st⟩ :
      Option (TM2.Cfg (Alphabet A B) (Label Q A) (State Q A B))))
      (update_input (A := A) [] [] w [])
  | cons a v ih =>
    have ht := steps_trans (emit_steps initial q next emit a v w)
      (ih (next q a) ((emit q a).reverse++w))
    convert ht using 1 <;> simp [output,List.reverse_append,List.append_assoc]
    omega

variable [Fintype A] [Fintype B] [Fintype Q]

def outputsInTime (initial : Q) (next : Q → A → Q) (emit : Q → A → List B) (v : List A) :
    TM2OutputsInTime (machine initial next emit) v (some (output next emit initial v))
      (2*v.length+(output next emit initial v).length+2) := by
  have h₁ := read_steps initial initial next emit v []
  simp only [List.append_nil] at h₁
  have h := steps_trans h₁
    (reverse_steps initial next emit ((output next emit initial v).reverse) [] (initial,none,none))
  have hi : initList (machine initial next emit) v=
      ⟨some .read,(initial,none,none),tapes v [] []⟩ := by
    change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
    congr 1
    funext k; cases k <;> rfl
  have ho : haltList (machine initial next emit) (output next emit initial v)=
      ⟨none,(initial,none,none),tapes [] [] (output next emit initial v)⟩ := by
    change TM2.Cfg.mk _ _ _=TM2.Cfg.mk _ _ _
    congr 1
    funext k; cases k <;> rfl
  apply steps_timed (n := (2*v.length+1)+((output next emit initial v).reverse.length+1))
  · change Steps (TM2.step (program initial next emit)) _ _ _
    simp only [hi,ho,List.append_nil,List.reverse_reverse] at h ⊢
    exact h
  · simp only [List.length_reverse]; omega

end MinUncut.Costed.WordTransducer

namespace MinUncut.Costed
open _root_.Turing _root_.Turing.ToPartrec _root_.Turing.PartrecToTM2
  _root_.OAI.Turing.PartrecToTM2 Function
open _root_.Turing.PartrecToTM2.K'

theorem head_tail_length (v : List ℕ) :
    (trNat v.headI).length+(trList v.tail).length ≤ bitsize v := by
  cases v <;> simp [bitsize,trList]

theorem head_length (v : List ℕ) : (trNat v.headI).length ≤ bitsize v :=
  (Nat.le_add_right _ _).trans (head_tail_length v)

theorem tail_length (v : List ℕ) : bitsize v.tail ≤ bitsize v :=
  (Nat.le_add_left _ _).trans (head_tail_length v)

theorem save_steps (f fs : Code) (k : Cont') (v : List ℕ) (s : Option Γ') (S : List Γ') :
    Steps (TM2.step tr) (2*bitsize v+3)
      ⟨some (trNormal (.cons f fs) k),s,K'.elim (trList v) [] [] S⟩
      ⟨some (trNormal f (.cons₁ fs k)),none,
        K'.elim (trList v) [] [] (trList v ++ Γ'.consₗ::S)⟩ := by
  have he : 2*bitsize v+3=((trList v).length+1)+((trList v).length+1)+1 := by
    simp only [bitsize]; omega
  rw [he]
  refine steps_head rfl (steps_trans (move_steps (by decide) (splitAtPred_false _)) ?_)
  simp only [elim_stack,elim_update_stack,elim_update_main,elim_rev,elim_update_rev]
  simpa [List.reverseAux_eq] using
    (copy_steps (trNormal f (.cons₁ fs k)) none [] (trList v).reverse [] (Γ'.consₗ::S))

theorem swap_steps (fs : Code) (k : Cont') (v u : List ℕ) (s : Option Γ') (S : List Γ') :
    Steps (TM2.step tr) (4*bitsize u+2*bitsize v+10)
      ⟨some (Λ'.ret (.cons₁ fs k)),s,
        K'.elim (trList u) [] [] (trList v ++ Γ'.consₗ::S)⟩
      ⟨some (trNormal fs (.cons₂ k)),none,
        K'.elim (trList v) [] [] (trList u ++ Γ'.consₗ::S)⟩ := by
  have he : 4*bitsize u+2*bitsize v+10 =
      (2*(trList u).length+3)+((2*(trList v).length+3)+(2*(trList u).length+3))+1 := by
    simp only [bitsize]; omega
  rw [he]
  refine steps_head rfl (steps_trans (move₂_steps (by decide) rfl (splitAtPred_false _)) ?_)
  simp only [Option.elim,id_eq,elim_update_main,elim_aux,
    List.append_nil,elim_update_aux]
  refine steps_trans (move₂_steps (o := some Γ'.consₗ) (L₂ := S) (by decide) rfl ?_) ?_
  · exact splitAtPred_eq _ _ (trList v) (some Γ'.consₗ) S
      (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl,rfl⟩
  simpa only [Option.elim,List.append_nil,elim_update_stack,elim_main,
    elim_update_main,id_eq,elim_update_aux,elim_aux,elim_stack] using
    (move₂_steps (q := trNormal fs (.cons₂ k)) (s := none)
      (p := fun _ => false) (k₁ := aux) (k₂ := stack)
      (S := K'.elim (trList v) [] (trList u) (Γ'.consₗ::S))
      (by decide) rfl (splitAtPred_false _))

theorem fix_done_steps (f : Code) (k : Cont') (v : List ℕ) (s : Option Γ') (S : List Γ')
    (hv : v.headI=0) :
    Steps (TM2.step tr) 1
      ⟨some (Λ'.ret (.fix f k)),s,K'.elim (trList v) [] [] S⟩
      ⟨some (Λ'.ret k),(trList v).head?,K'.elim (trList v.tail) [] [] S⟩ := by
  apply steps_one
  cases v with
  | nil => simp [TM2.step]
  | cons a v =>
    simp only [List.headI_cons] at hv
    subst a
    simp [TM2.step]

theorem fix_more_steps (f : Code) (k : Cont') (a : ℕ) (v : List ℕ) (s : Option Γ') (S : List Γ') :
    Steps (TM2.step tr) ((trNat (a+1)).length+1)
      ⟨some (Λ'.ret (.fix f k)),s,K'.elim (trList ((a+1)::v)) [] [] S⟩
      ⟨some (trNormal f (.fix f k)),some Γ'.cons,K'.elim (trList v) [] [] S⟩ := by
  have htt : natEnd ((trList ((a+1)::v)).head?.getD default)=false ∧
      (trList ((a+1)::v)).tail=(trNat (a+1)).tail ++ Γ'.cons::trList v := by
    simp only [trList,trNat.eq_1,Nat.cast_succ,Num.add_one,Num.succ]
    cases (a : Num).succ' <;> exact ⟨rfl,rfl⟩
  have hn : (trNat (a+1)).length=(trNat (a+1)).tail.length+1 := by
    simp only [trNat.eq_1,Nat.cast_succ,Num.add_one,Num.succ]
    cases (a : Num).succ' <;> simp [trNum,trPosNum]
  rw [hn]
  refine steps_head rfl ?_
  rw [tr]; simp only [TM2.stepAux,pop',elim_main,htt.1]
  convert! (clear_steps (q := trNormal f (.fix f k))
    (s := (trList ((a+1)::v)).head?) (k := main)
    (S := K'.elim (trList ((a+1)::v)).tail [] [] S)
    (splitAtPred_eq _ _ (trNat (a+1)).tail (some Γ'.cons) (trList v)
      (fun x h => trNat_natEnd _ _ (List.tail_subset _ h)) ⟨rfl,htt.2⟩)) using 2 <;> simp

theorem CodeRun.compiled {c v w t} (h : CodeRun c v w t)
    (k : Cont') (s : Option Γ') (S : List Γ') : ∃ s',
    Within (TM2.step tr) t
      ⟨some (trNormal c k),s,K'.elim (trList v) [] [] S⟩
      ⟨some (Λ'.ret k),s',K'.elim (trList w) [] [] S⟩ := by
  induction h generalizing k s S with
  | zero v => exact ⟨s,within_one (by simp [TM2.step])⟩
  | succ v =>
    refine ⟨none,?_⟩
    have hh := (head_main_steps (q := Λ'.succ (.ret k)) (s := s) (L := v)
      (c := []) (d := S)).within.trans (succ_time (n := v.headI))
    exact hh.mono (by have hv := head_tail_length v; dsimp [bitsize] at *; omega)
  | tail v =>
    let o : Option Γ' := List.casesOn v none fun _ _ => some Γ'.cons
    refine ⟨o,?_⟩
    have hh : Steps (TM2.step tr) ((trNat v.headI).length+1)
        ⟨some (trNormal .tail k),s,K'.elim (trList v) [] [] S⟩
        ⟨some (.ret k),o,K'.elim (trList v.tail) [] [] S⟩ := by
      convert! (clear_steps (q := .ret k) (s := s) (k := main)
        (S := K'.elim (trList v) [] [] S)
        (splitAtPred_eq _ _ (trNat v.headI) o (trList v.tail) (trNat_natEnd _) ?_)) using 2
      · simp
      · dsimp [o]
        cases v <;> exact ⟨rfl,rfl⟩
    exact hh.within.mono (by have hv := head_length v; omega)
  | @cons f fs v u w t t' hf hfs ih ih' =>
    obtain ⟨s₁,h₁⟩ := ih (.cons₁ fs k) none (trList v ++ Γ'.consₗ::S)
    obtain ⟨s₂,h₂⟩ := ih' (.cons₂ k) none (trList u ++ Γ'.consₗ::S)
    have h₃ := (save_steps f fs k v s S).within.trans h₁
    have h₄ := h₃.trans (swap_steps fs k v u s₁ S).within
    have h₅ := h₄.trans h₂
    have h₆ : Within (TM2.step tr) (2*bitsize u+6+1)
        ⟨some (.ret (.cons₂ k)),s₂,K'.elim (trList w) [] [] (trList u ++ Γ'.consₗ::S)⟩
        ⟨some (.ret k),none,K'.elim (trList (u.headI::w)) [] [] S⟩ :=
      (head_stack_time (q := .ret k) (s := s₂) (L₁ := w) (L₂ := u) (L₃ := S)).head rfl
    exact ⟨none,(h₅.trans h₆).mono (by omega)⟩
  | @comp f g v u w t t' hg hf ih ih' =>
    obtain ⟨s₁,h₁⟩ := ih (.comp f k) s S
    obtain ⟨s₂,h₂⟩ := ih' k s₁ S
    exact ⟨s₂,(h₁.trans (h₂.head rfl)).mono (by omega)⟩
  | @caseZero f g v w t hz hf ih =>
    obtain ⟨s₁,h₁⟩ := pred_time (trNormal f k) (trNormal g k) s v [] S
    simp only [hz,Nat.rec_zero] at h₁
    obtain ⟨s₂,h₂⟩ := ih k s₁ S
    exact ⟨s₂,(h₁.trans h₂).mono (by dsimp [bitsize]; omega)⟩
  | @caseSucc f g v a w t hg ih =>
    obtain ⟨s₁,h₁⟩ := pred_time (trNormal f k) (trNormal g k) s ((a+1)::v) [] S
    simp only [List.headI_cons,List.tail_cons] at h₁
    obtain ⟨s₂,h₂⟩ := ih k s₁ S
    exact ⟨s₂,(h₁.trans h₂).mono (by dsimp [bitsize]; omega)⟩
  | @fixDone f v u t hf hu ih =>
    obtain ⟨s₁,h₁⟩ := ih (.fix f k) s S
    exact ⟨(trList u).head?,h₁.trans (fix_done_steps f k u s₁ S hu).within⟩
  | @fixMore f v u a w t t' hf hr ih ih' =>
    obtain ⟨s₁,h₁⟩ := ih (.fix f k) s S
    obtain ⟨s₂,h₂⟩ := ih' k (some Γ'.cons) S
    exact ⟨s₂,((h₁.trans (fix_more_steps f k a u s₁ S).within).trans h₂).mono
      (by dsimp [bitsize]; simp only [List.length_append,List.length_cons]; omega)⟩

open _root_.Turing
namespace FiniteControl
variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

noncomputable def stmt (S : Finset Λ) :
    (q : TM2.Stmt Γ Λ σ) → TM2.SupportsStmt S q → TM2.Stmt Γ S σ
  | .push k f q, h => .push k f (stmt S q h)
  | .peek k f q, h => .peek k f (stmt S q h)
  | .pop k f q, h => .pop k f (stmt S q h)
  | .load f q, h => .load f (stmt S q h)
  | .branch f q r, h => .branch f (stmt S q h.1) (stmt S r h.2)
  | .goto f, h => .goto (fun s => ⟨f s,h s⟩)
  | .halt, _ => .halt

def project (S : Finset Λ) (c : TM2.Cfg Γ S σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l.map Subtype.val,c.var,c.stk⟩

omit [DecidableEq K] in
lemma project_injective (S : Finset Λ) : Function.Injective (project (Γ:=Γ) (σ:=σ) S) := by
  intro a b h
  cases a with | mk a v A =>
    cases b with | mk b w B =>
      simp only [project,TM2.Cfg.mk.injEq] at h
      rcases h with ⟨h,hv,hB⟩
      have hab : a=b := Option.map_injective Subtype.val_injective h
      cases hab; cases hv; cases hB; rfl

lemma project_aux (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q)
    (s : σ) (st : ∀ k,List (Γ k)) :
    project S (TM2.stepAux (stmt S q h) s st)=TM2.stepAux q s st := by
  induction q generalizing s st with
  | push k f q ih => exact ih h _ _
  | peek k f q ih => exact ih h _ _
  | pop k f q ih => exact ih h _ _
  | load f q ih => exact ih h _ _
  | branch f q r ih ih' =>
    cases he : f s <;> simp only [stmt,TM2.stepAux,he,
      Bool.cond_false,Bool.cond_true] <;> first | exact ih h.1 _ _ | exact ih' h.2 _ _
  | goto f => rfl
  | halt => rfl

noncomputable def program (S : Finset Λ) (m : Λ → TM2.Stmt Γ Λ σ)
    (h : ∀q∈S,TM2.SupportsStmt S (m q)) : S → TM2.Stmt Γ S σ :=
  fun q => stmt S (m q.val) (h q q.property)

lemma project_step (S : Finset Λ) (m : Λ → TM2.Stmt Γ Λ σ)
    (h : ∀q∈S,TM2.SupportsStmt S (m q)) (c : TM2.Cfg Γ S σ) :
    (TM2.step (program S m h) c).map (project S)=TM2.step m (project S c) := by
  rcases c with ⟨l,s,st⟩
  cases l with
  | none => rfl
  | some q => exact congrArg some (project_aux S (m q) (h q q.property) s st)

lemma projected_iterate {α β : Type} (f : α → Option α) (g : β → Option β)
    (p : α → β) (h : ∀a,(f a).map p=g (p a)) (n : ℕ) (a : Option α) :
    ((fun x => x.bind f)^[n] a).map p=(fun x => x.bind g)^[n] (a.map p) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply,ih]
    congr 1
    cases a with
    | none => rfl
    | some a => exact h a

end FiniteControl
end MinUncut.Costed

end OAI
