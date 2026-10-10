import OAI.Computability.SpaceSimulation.Register.Loop
import OAI.Computability.SpaceSimulation.Stack.Count

namespace OAI

namespace Fifths
namespace Comp
variable {X I : Type} {x : I → List X} {S a b : I → ℕ}
open Bin

theorem ticks (inc : Bool) (h : Fits S a) : Comp x S a
    (fun i => if inc then a i + 1 else a i - 1) := by
  let k : Unit ⊕ Unit := .inl ()
  let t : Unit ⊕ Unit := .inr ()
  refine checkSized (SM.carry inc k t) h (fun i B p => ?_)
  let v := singleton Unit (a i)
  have r : v.ok B := Store.ok_extra.mpr (file_ok.mpr
    (le_trans (Nat.le_succ _) p))
  have l : (v.st k).length + (v.st t).length + 1 ≤ B := by
    change (a i).bits.length + 0 + 1 ≤ B
    simpa only [Nat.add_zero, Nat.size_eq_bits_len] using p
  have e := SM.exec_carry (i := files (x i)) inc k t (by simp [k,t]) r l
  have g : SM.carried v inc k t =
      singleton Unit (if inc then a i+1 else a i-1) := by
    unfold SM.carried
    rw [show v.set t [] = v from Store.set_self v t]
    rw [show v.st t = [] from rfl, List.reverse_nil, List.nil_append,
      show v.st k = (a i).bits from rfl]
    cases inc
    · rw [tick_dec]; exact singleton_set _ _ _
    · rw [tick_inc]; exact singleton_set _ _ _
  rw [g] at e
  exact e

theorem plus1 (h : Comp x S a b) : Comp x S a (fun i => b i + 1) :=
  h.trans (ticks true h.target)
theorem minus1 (h : Comp x S a b) : Comp x S a (fun i => b i - 1) :=
  h.trans (ticks false h.target)

def notZero (n : ℕ) : Bool := n != 0

theorem notZero_eq (n : ℕ) : n.bits.head?.isSome = notZero n := by
  by_cases h : n = 0
  · subst n; simp [notZero]
  have e : n.bits ≠ [] := by simpa using h
  cases v : n.bits with
  | nil => contradiction
  | cons a b => simp [notZero,h]

theorem testnz (h : Comp x S a b) :
    Comp x S a (fun i => (notZero (b i)).toNat) := by
  refine h.trans ?_
  let k : Unit ⊕ Unit := .inl ()
  let M (c : Bool) : SM X Empty (Unit ⊕ Unit) Unit :=
    (SM.clear k).seq (SM.prepend k c.toNat.bits)
  refine checkSized ((SM.peek (fun _ s => (s k).isSome)).bind M)
    h.target (fun i B p => ?_)
  let v := singleton Unit (b i)
  have o : v.ok B := Store.ok_extra.mpr (file_ok.mpr (le_trans (Nat.le_succ _) p))
  have eqn := (show (v.see k).isSome = notZero (b i) from notZero_eq _)
  refine SM.exec_bind _ _ (y := notZero (b i))
    (show (SM.peek _).Exec (files (x i)) B v v _ from eqn ▸ SM.exec_peek o) ?_
  have e := SM.exec_clear (i := files (x i)) k o
  have g (c : Bool) : (M c).Exec (files (x i)) B v
      (singleton Unit c.toNat) () := by
    have j : B ≥ 1 := by omega
    have u := SM.exec_prepend (i := files (x i)) k c.toNat.bits e.endOk
      (by cases c <;> simp [j])
    simp only [Store.set_same,List.append_nil,Store.set_set] at u
    rw [show k = .inl () from rfl,singleton_set] at u
    exact SM.exec_seq e u
  exact g _

/-- Accumulating loop. PC logic keeps the original argument, a
remaining count, a current index, and the accumulator. Time for the
counted loop is not charged. -/
theorem fold {n : I → ℕ} (v : I → ℕ → ℕ) (cnt : Comp x S a n)
    (ini : Comp x S a (fun i => v i 0))
    (sizes : Fits (fun i : Through n => S i.1.1) (fun i => v i.1.1 i.1.2))
    (advance : ∀ e : Before n → ℕ,
      Comp (fun i : Before n => x i.1.1) (fun i => S i.1.1) e (fun i => a i.1.1) →
      Comp (fun i : Before n => x i.1.1) (fun i => S i.1.1) e (fun i => i.1.2) →
      Comp (fun i : Before n => x i.1.1) (fun i => S i.1.1) e (fun i => v i.1.1 i.1.2) →
      Comp (fun i : Before n => x i.1.1) (fun i => S i.1.1) e
        (fun i => v i.1.1 (i.1.2+1))) :
    Comp x S a (fun i => v i (n i)) := by
  let z : I → ℕ → ℕ :=
    fun i j => Bin.pair (a i) (Bin.pair j (Bin.pair (n i-j) (v i j)))
  have c : Comp x S a (fun i => z i 0) :=
    ((Comp.refl cnt.source).pair
      ((Comp.constant cnt.source 0).pair (cnt.pair ini)))
  suffices w : Comp x S (fun i => z i 0) (fun i => z i (n i)) from
    (c.trans w).right.right.right
  have zsize : Fits (fun i : Through n => S i.1.1) (fun i => z i.1.1 i.1.2) := by
    let f : Through n → I := fun i => i.1.1
    have h := cnt.target.pull f
    refine (cnt.source.pull f).pair ((h.mono ?_).pair ((h.mono ?_).pair sizes))
    · exact fun i => i.2
    · intro i
      exact Nat.sub_le _ _
  apply loop n z
  · let f : Before n → Through n := fun i => ⟨i.val,i.property.le⟩
    have h : Comp (fun i : Before n => x i.1.1) (fun i => S i.1.1)
        (fun i => z i.1.1 i.1.2) (fun i => z i.1.1 i.1.2) :=
      Comp.refl (zsize.pull f)
    have w := advance _ h.left h.right.left h.right.right.right
    have g := h.left.pair
      (h.right.left.plus1.pair (h.right.right.left.minus1.pair w))
    exact g.congr (fun i => by
      rw [show n i.1.1-i.1.2-1 = n i.1.1 - (i.1.2+1) by omega])
  · have h : Comp (fun i : Through n => x i.1.1) (fun i => S i.1.1)
        (fun i => z i.1.1 i.1.2) (fun i => z i.1.1 i.1.2) :=
      Comp.refl zsize
    refine h.right.right.left.testnz.congr (fun i => ?_)
    by_cases e : i.1.2 < n i.1.1
    · simp [notZero,e,Nat.ne_of_gt (Nat.sub_pos_of_lt e)]
    · simp [notZero,e,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt e)]

end Comp
end Fifths

end OAI
