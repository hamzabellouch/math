import OAI.NumberTheory.Ostmann.Arithmetic.MovingNodeUnits
import OAI.NumberTheory.Ostmann.Construction.ModularAdaptiveSupport

namespace OAI

/-! # Paths in the frequency-only arithmetic recursion

These states follow `movingFrequencyGate`, whose pivots invert the fixed
compensation modulo a power of the frequency modulus.
-/

namespace Ostmann
open scoped Classical

structure FrequencyModelState (σ : Type*) where
  level : ℕ
  data : MovingSlotData σ level
  leftGiant : ℤ
  rightGiant : ℤ

def FrequencyModelState.pivot {σ : Type*} (value : σ → ℕ) (R : ℤ) :
    FrequencyModelState σ → ℤ
  | ⟨0, _, _, _⟩ => 0
  | ⟨n + 1, .node s CL CR U l r, x, y⟩ =>
      (MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y

def FrequencyModelState.frequencies {σ : Type*} : FrequencyModelState σ → NodeFrequencies
  | ⟨0, .leaf s _, _, _⟩ => ⟨s, s, s⟩
  | ⟨_ + 1, .node s _ _ _ l r, _, _⟩ => ⟨s, l.frequency, r.frequency⟩

def frequencyModelAtPath {σ : Type*} (value : σ → ℕ) (R : ℤ) :
    (n : ℕ) → MovingSlotData σ n → ℤ → ℤ → List Bool → FrequencyModelState σ
  | 0, T, x, y, _ => ⟨0, T, x, y⟩
  | n + 1, T@(.node s CL CR U l r), x, y, path =>
      match path with
      | [] => ⟨n + 1, T, x, y⟩
      | b :: path =>
          let p := (MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y
          if b then frequencyModelAtPath value R n r p y path
          else frequencyModelAtPath value R n l p x path

theorem frequencyModelAtPath_level {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (path : List Bool) (hp : path.length < n) :
    (frequencyModelAtPath value R n T x y path).level + path.length = n := by
  induction n generalizing x y path with
  | zero => simp at hp
  | succ n ih =>
    cases T with
    | node s CL CR U l r =>
      cases path with
      | nil => rfl
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        cases b <;> simp only [frequencyModelAtPath, Bool.false_eq_true, ite_false, ite_true,
          List.length_cons]
        · have := ih l ((MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y) x path hp'; omega
        · have := ih r ((MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y) y path hp'; omega

theorem frequencyModelAtPath_gate {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (n : ℕ) (T : MovingSlotData σ n) (x y : ℤ) (path : List Bool)
    (h : movingFrequencyGate value R T x y) :
    let z := frequencyModelAtPath value R n T x y path
    movingFrequencyGate value R z.data z.leftGiant z.rightGiant := by
  induction n generalizing x y path with
  | zero => cases T; exact h
  | succ n ih =>
    cases T with
    | node s CL CR U l r =>
      cases path with
      | nil => exact h
      | cons b path =>
        cases b
        · exact ih l _ x path h.2.2.1
        · exact ih r _ y path h.2.2.2

theorem frequencyModelAtPath_frequencies {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (S : Finset ℤ) (n : ℕ) (T : MovingSlotData σ n) (t : FrequencyTree S n)
    (hT : T.Follows (frequencyTreeMap Subtype.val n t))
    (x y : ℤ) (path : List Bool) (hp : path.length < n) :
    (frequencyModelAtPath value R n T x y path).frequencies =
      singleTreeNodeFrequencies S n t (nodePathIndex n path) := by
  induction n generalizing x y path with
  | zero => simp at hp
  | succ n ih =>
    cases T with
    | node s CL CR U l r =>
      cases path with
      | nil =>
        change NodeFrequencies.mk s l.frequency r.frequency = _
        rw [hT.1, hT.2.1.root, hT.2.2.root]
        simp only [frequencyTreeMap, frequencyRoot_map, nodePathIndex,
          singleTreeNodeFrequencies, singleFrequencySplitList, List.getD_cons_zero]
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        have hidx := nodePathIndex_lt n path hp'
        have hlen := singleFrequencySplitList_length S n t.2.1
        cases b
        · change (frequencyModelAtPath value R n l _ x path).frequencies = _
          rw [ih l t.2.1 hT.2.1 _ x path hp']
          unfold singleTreeNodeFrequencies
          simp only [nodePathIndex, Bool.false_eq_true, ite_false, singleFrequencySplitList]
          rw [show 1 + nodePathIndex n path = nodePathIndex n path + 1 by omega,
            List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa only [hlen] using hidx)]
        · change (frequencyModelAtPath value R n r _ y path).frequencies = _
          rw [ih r t.2.2 hT.2.2 _ y path hp']
          unfold singleTreeNodeFrequencies
          simp only [nodePathIndex, ite_true, singleFrequencySplitList]
          rw [show 2 ^ n + nodePathIndex n path = (2 ^ n - 1 + nodePathIndex n path) + 1 by
              have := Nat.one_le_two_pow (n := n); omega,
            List.getD_cons_succ, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
          rw [show 2 ^ n - 1 + nodePathIndex n path - (2 ^ n - 1) = nodePathIndex n path by omega]

end Ostmann

end OAI
