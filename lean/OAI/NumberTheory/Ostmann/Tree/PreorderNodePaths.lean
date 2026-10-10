import OAI.NumberTheory.Ostmann.Construction.AncestorPivotPrecision
import OAI.NumberTheory.Ostmann.Arithmetic.SingleFrequencyTree

namespace OAI

/-! # Explicit preorder indices for internal nodes and their ancestors -/

namespace Ostmann

/-- `false` descends left, `true` descends right. -/
def nodePathIndex : ℕ → List Bool → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, b :: p => (if b then 2 ^ n else 1) + nodePathIndex n p

theorem nodePathIndex_lt (n : ℕ) (p : List Bool) (hp : p.length < n) :
    nodePathIndex n p < 2 ^ n - 1 := by
  induction n generalizing p with
  | zero => simp at hp
  | succ n ih =>
    cases p with
    | nil =>
      simp only [nodePathIndex]
      have := Nat.one_le_two_pow (n := n)
      rw [pow_succ]
      omega
    | cons b p =>
      have hp' : p.length < n := by simpa using hp
      have hi := ih p hp'
      have := Nat.one_le_two_pow (n := n)
      cases b <;> simp only [nodePathIndex, Bool.false_eq_true, ite_false, ite_true]
      all_goals rw [pow_succ]; omega

def preorderNodePath : (n : ℕ) → Fin (2 ^ n - 1) → List Bool
  | 0, j => Fin.elim0 j
  | n + 1, j =>
      if h0 : j.val = 0 then []
      else if hL : j.val < 2 ^ n then
        false :: preorderNodePath n ⟨j.val - 1, by omega⟩
      else true :: preorderNodePath n ⟨j.val - 2 ^ n, by
        have hj : j.val < 2 ^ n * 2 - 1 := by
          calc
            j.val < 2 ^ (n + 1) - 1 := j.isLt
            _ = 2 ^ n * 2 - 1 := by rw [pow_succ]
        have := Nat.one_le_two_pow (n := n)
        omega⟩

theorem preorderNodePath_length (n : ℕ) (j : Fin (2 ^ n - 1)) :
    (preorderNodePath n j).length < n := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    simp only [preorderNodePath]
    split_ifs
    · simp
    · simpa only [List.length_cons, Nat.add_lt_add_iff_right] using ih _
    · simpa only [List.length_cons, Nat.add_lt_add_iff_right] using ih _

theorem nodePathIndex_preorderNodePath (n : ℕ) (j : Fin (2 ^ n - 1)) :
    nodePathIndex n (preorderNodePath n j) = j.val := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    simp only [preorderNodePath]
    split_ifs with h0 hL
    · exact h0.symm
    · simp only [nodePathIndex, Bool.false_eq_true, ite_false, ih]
      omega
    · simp only [nodePathIndex, ite_true, ih]
      omega

theorem preorderNodePath_nodePathIndex (n : ℕ) (p : List Bool) (hp : p.length < n) :
    preorderNodePath n ⟨nodePathIndex n p, nodePathIndex_lt n p hp⟩ = p := by
  induction n generalizing p with
  | zero => simp at hp
  | succ n ih =>
    cases p with
    | nil => simp [nodePathIndex, preorderNodePath]
    | cons b p =>
      have hp' : p.length < n := by simpa using hp
      have hi := nodePathIndex_lt n p hp'
      have hpow := Nat.one_le_two_pow (n := n)
      cases b
      · have hzero : 1 + nodePathIndex n p ≠ 0 := by omega
        have hleft : 1 + nodePathIndex n p < 2 ^ n := by omega
        simp only [nodePathIndex, Bool.false_eq_true, ite_false, preorderNodePath,
          hzero, dite_false, hleft, dite_true]
        congr 1
        simpa only [Nat.add_sub_cancel_left] using ih p hp'
      · have hzero : 2 ^ n + nodePathIndex n p ≠ 0 := by positivity
        have hleft : ¬2 ^ n + nodePathIndex n p < 2 ^ n := by omega
        simp only [nodePathIndex, ite_true, preorderNodePath, hzero, dite_false, hleft]
        congr 1
        simpa only [Nat.add_sub_cancel_left] using ih p hp'

theorem nodePathIndex_nonempty_pos (n : ℕ) (p : List Bool)
    (hp : p.length < n) (hne : p ≠ []) : 0 < nodePathIndex n p := by
  cases n with
  | zero => simp at hp
  | succ n =>
    cases p with
    | nil => exact False.elim (hne rfl)
    | cons b p =>
      have := Nat.one_le_two_pow (n := n)
      cases b <;> simp only [nodePathIndex, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem nodePathIndex_proper_prefix (n : ℕ) (p s : List Bool)
    (hps : (p ++ s).length < n) (hs : s ≠ []) :
    nodePathIndex n p < nodePathIndex n (p ++ s) := by
  induction n generalizing p with
  | zero => simp at hps
  | succ n ih =>
    cases p with
    | nil =>
      simpa only [List.nil_append, nodePathIndex] using nodePathIndex_nonempty_pos (n + 1) s hps hs
    | cons b p =>
      have hi := ih p (by simpa only [List.cons_append, List.length_cons, Nat.add_lt_add_iff_right] using hps)
      simp only [List.cons_append, nodePathIndex]
      exact Nat.add_lt_add_left hi _

end Ostmann

end OAI
