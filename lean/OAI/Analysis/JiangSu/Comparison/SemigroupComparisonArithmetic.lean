import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

section

namespace Pureness
namespace OrderedSemigroup
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

theorem iterate_with_buffer {a b c : S} (h : a + c ≤ b + c) (n : ℕ) :
    n • a + c ≤ n • b + c := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (n+1) • a + c = a + (n • a + c) := by simp [succ_nsmul, add_comm, add_left_comm]
      _ ≤ a + (n • b + c) := add_le_add le_rfl ih
      _ = n • b + (a + c) := by ac_rfl
      _ ≤ n • b + (b + c) := add_le_add le_rfl h
      _ = (n+1) • b + c := by simp [succ_nsmul, add_assoc]

theorem strict_multiples_le
    (hzero : ∀ a : S, 0 ≤ a)
    (hAU : ∀ a b : S, ∀ k : ℕ, 1 ≤ k → (k+1) • a ≤ k • b → a ≤ b)
    {a b : S} {m n : ℕ} (hmn : m < n) (h : n • a ≤ m • b) : a ≤ b := by
  by_cases hm : m = 0
  · subst m
    have ha : a ≤ n • a := by
      simpa only [one_nsmul] using nsmul_le_nsmul_left (hzero a) (show 1 ≤ n by omega)
    exact ha.trans (by simpa using h) |>.trans (hzero b)
  · apply hAU a b m (by omega)
    exact (nsmul_le_nsmul_left (hzero a) (show m+1 ≤ n by omega)).trans h

theorem strict_multiples_le_of_buffer
    (hzero : ∀ a : S, 0 ≤ a)
    (hAU : ∀ a b : S, ∀ k : ℕ, 1 ≤ k → (k+1) • a ≤ k • b → a ≤ b)
    {a b c : S} {m n k : ℕ} (hmn : m < n)
    (h : n • a + c ≤ m • b + c) (hc : c ≤ k • b) : a ≤ b := by
  have hi := iterate_with_buffer h (k+1)
  have hcomp : ((k+1)*n) • a ≤ ((k+1)*m+k) • b := by
    calc
      ((k+1)*n) • a ≤ ((k+1)*n) • a + c := le_add_of_nonneg_right (hzero c)
      _ ≤ ((k+1)*m) • b + c := by simpa only [← mul_nsmul, Nat.mul_comm] using hi
      _ ≤ ((k+1)*m) • b + k • b := add_le_add le_rfl hc
      _ = ((k+1)*m+k) • b := (add_nsmul _ _ _).symm
  apply strict_multiples_le hzero hAU (m := (k+1)*m+k) (n := (k+1)*n) _ hcomp
  nlinarith

theorem properlyInfinite_of_multiple
    (hzero : ∀ a : S, 0 ≤ a)
    (hAU : ∀ a b : S, ∀ k : ℕ, 1 ≤ k → (k+1) • a ≤ k • b → a ≤ b)
    {u : S} {k : ℕ} (hk : 0 < k) (h : (2*k) • u ≤ k • u) : 2 • u ≤ u := by
  have hstep : (k+1) • u ≤ k • u :=
    (nsmul_le_nsmul_left (hzero u) (by omega : k+1 ≤ 2*k)).trans h
  have hi : ∀ j : ℕ, (k+j) • u ≤ k • u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        (k+(j+1)) • u = (k+j) • u + u := by simp [add_nsmul, add_assoc]
        _ ≤ k • u + u := add_le_add ih le_rfl
        _ = (k+1) • u := by simp [add_nsmul]
        _ ≤ k • u := hstep
  apply hAU (2 • u) u k (by omega)
  simpa only [← mul_nsmul, show 2*(k+1) = k+(k+2) by omega] using hi (k+2)

theorem le_of_properlyInfinite {u a : S} (hu : 2 • u ≤ u)
    (ha : ∃ n : ℕ, a ≤ n • u) (hzero : 0 ≤ u) : a ≤ u := by
  obtain ⟨n, hn⟩ := ha
  apply hn.trans
  clear hn
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    calc
      (n+1) • u = n • u + u := by simp [add_nsmul]
      _ ≤ u + u := add_le_add ih le_rfl
      _ ≤ u := by simpa [two_nsmul] using hu

end OrderedSemigroup
end Pureness
end

end OAI
