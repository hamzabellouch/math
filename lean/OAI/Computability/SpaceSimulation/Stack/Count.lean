import OAI.Computability.SpaceSimulation.Stack.Edit
import OAI.Computability.SpaceSimulation.Binary

namespace OAI

/-! Unbounded binary increment and decrement. Simple stack algorithms. -/

namespace Fifths
namespace Bin
/-- Write at most one bit before the uncopied high bits. -/
def lastDigit (inc more : Bool) : List Bool :=
  if inc || more then [inc] else []

def tick (inc : Bool) : List Bool → List Bool
  | [] => lastDigit inc false
  | b :: l =>
    if b = inc then (!b) :: tick inc l
    else lastDigit inc l.head?.isSome ++ l

theorem tick_inc (n : ℕ) : tick true n.bits = (n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [tick,lastDigit]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    cases b with
    | false =>
      change tick true _ = (2*n + 1).bits
      simp [tick,lastDigit]
    | true =>
      change tick true _ = (2*n+1+1).bits
      rw [show 2*n+1+1 = 2*(n+1) by omega]
      simp [tick,ih]

theorem tick_dec (n : ℕ) : tick false n.bits = (n-1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [tick,lastDigit]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    cases b with
    | false =>
      have q : n ≠ 0 := by simpa using h
      change tick false _ = (2*n - 1).bits
      rw [show 2*n-1 = 2*(n-1)+1 by omega]
      simp [tick,ih]
    | true =>
      change tick false _ = (2*n + 1 - 1).bits
      by_cases q : n = 0
      · subst n; simp [tick,lastDigit]
      · have e : n.bits.head?.isSome := by
          have g : n.bits ≠ [] := by simpa using q
          cases r : n.bits
          · contradiction
          · simp
        simp [tick,lastDigit,e,q]
end Bin

namespace SM
open Bin
variable {X J K : Type} [DecidableEq K]

def finishDigit (inc : Bool) (k : K) : SM X J K Unit :=
  (peek (fun _ t => (t k).isSome)).bind (fun b => prepend k (lastDigit inc b))

def finish (inc : Bool) (k t : K) : SM X J K (Option Unit) :=
  (finishDigit inc k).seq ((spill t k).seq (pure (some ())))

def continueCarry (inc : Bool) (k t : K) : Option Bool → SM X J K (Option Unit)
  | none => finish inc k t
  | some b => if b = inc then
      (prepend t [!b]).seq (pure none)
    else finish inc k t

def carry (inc : Bool) (k t : K) : SM X J K Unit :=
  ((pop k).bind (continueCarry inc k t)).loop

theorem exec_finish {i : Inputs X J} {s : Store J K} {B} (inc : Bool) (k t : K)
    (a : t ≠ k) (o : s.ok B) (p : (s.st k).length + (s.st t).length + 1 ≤ B) :
    (finish inc k t).Exec i B s
      ((s.set t []).set k ((s.st t).reverse ++
        (lastDigit inc (s.st k).head?.isSome ++ s.st k))) (some ()) := by
  let l := lastDigit inc (s.st k).head?.isSome ++ s.st k
  have h : l.length ≤ (s.st k).length + 1 := by
    cases inc <;> cases e : (s.st k).head? <;>
      simp [l,lastDigit,e]
  have e : (finishDigit inc k).Exec i B s (s.set k l) () :=
    exec_bind _ _ (exec_peek o)
      (exec_prepend k _ o (show l.length ≤ B by omega))
  have r := exec_spill (i := i) t k a e.endOk
    (by simp only [Store.set_other _ _ a, Store.set_same]; omega)
  have v := exec_seq e (exec_seq r (exec_pure (y := some ()) r.endOk))
  rw [Store.set_other _ _ a, Store.set_same, Store.set_swap s a, Store.set_set] at v
  exact v

def carried (s : Store J K) (inc : Bool) (k t : K) :=
  (s.set t []).set k ((s.st t).reverse ++ tick inc (s.st k))

theorem exec_carry {i : Inputs X J} {s : Store J K} {B}
    (inc : Bool) (k t : K)
    (a : t ≠ k) (o : s.ok B) (p : (s.st k).length + (s.st t).length + 1 ≤ B) :
    (carry inc k t).Exec i B s (carried s inc k t) () := by
  generalize e : s.st k = l
  induction l generalizing s with
  | nil =>
    have h : s.set k [] = s := by rw [← e]; simp
    have f : (pop k).Exec i B s s none := by
      simpa [e,h] using exec_pop (i := i) k o
    have g := exec_finish (i := i) inc k t a o p
    unfold carry
    refine loop_stop _ (exec_bind _ _ f ?_)
    simpa only [continueCarry,carried,e,tick,List.append_nil,List.head?_nil,Option.isSome_none]
      using g
  | cons b l ih =>
    let u := s.set k l
    have f : (pop k).Exec i B s u (some b) := by
      simpa [e,u] using exec_pop (i := i) k o
    have ul : u.st k = l := by simp [u]
    have y : u.st t = s.st t := by simp [u,a]
    by_cases c : b = inc
    · subst b
      let v := u.set t ((!inc) :: s.st t)
      have e' : ([!inc] ++ u.st t).length ≤ B := by
        simp [e] at p; simp only [y,List.cons_append,List.nil_append,List.length_cons]; omega
      have g : (prepend t [!inc]).Exec i B u v () := by
        simpa only [v,y,List.cons_append,List.nil_append] using
          exec_prepend (i := i) t _ f.endOk e'
      have vk : v.st k = l := by simp [v,a.symm,ul]
      have h := ih g.endOk (by simp [e] at p; simp only [vk,v,Store.set_same,List.length_cons];
                               omega) vk
      have r : carried s inc k t = carried v inc k t := by
        unfold carried
        simp only [vk,v,u,Store.set_same, Store.set_set,e,tick,ite_true,List.reverse_cons,
          List.append_assoc,List.cons_append,List.nil_append]
        rw [Store.set_swap s a, Store.set_set]
      rw [r]
      unfold carry
      refine loop_continue _ (exec_bind _ _ f ?_) h
      simpa only [continueCarry,ite_true] using
        exec_seq g (exec_pure (y := (none : Option Unit)) g.endOk)
    · have g := exec_finish (i := i) inc k t a f.endOk
        (by simp only [ul,y]; simp [e] at p; omega)
      unfold carry
      refine loop_stop _ (exec_bind _ _ f ?_)
      simp only [continueCarry,c,ite_false,carried,tick,e]
      simpa only [ul,y,u,Store.set_swap s a,Store.set_set] using g
end SM
end Fifths

end OAI
