import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Factorial closure of the kernel of a locally nilpotent derivation

This file formalizes `bun:factorial-closure` from Section 4 of the paper, using the highest nonzero iterates and the general Leibniz rule.
No exponential/action correspondence is needed for this elementary step.
-/

namespace StableCoordinate

open Finset Function

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- A derivation is locally nilpotent if each element is killed by some iterate. -/
def IsLocallyNilpotent (D : Derivation k A A) : Prop :=
  ∀ a : A, ∃ n : ℕ, (D : A → A)^[n] a = 0

/-- The general Leibniz formula for a ring derivation, with natural binomial coefficients. -/
theorem derivation_iterate_mul (D : Derivation k A A) (n : ℕ) (a b : A) :
    (D : A → A)^[n] (a * b) =
      ∑ ij ∈ antidiagonal n,
        n.choose ij.1 • ((D : A → A)^[ij.1] a * (D : A → A)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := A)
      (fun i j => (D : A → A)^[i] a * (D : A → A)^[j] b) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul,
      Derivation.leibniz, smul_eq_mul, smul_add, sum_add_distrib, add_right_inj]
    apply sum_congr rfl
    rintro ⟨i, j⟩ hij
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]
    rw [mul_comm]

/-- Once an iterate vanishes, all later iterates vanish. -/
theorem derivation_iterate_eq_zero_of_le (D : Derivation k A A) {a : A} {m n : ℕ}
    (hm : (D : A → A)^[m] a = 0) (hmn : m ≤ n) :
    (D : A → A)^[n] a = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_comm, Function.iterate_add_apply, hm]
  exact Function.iterate_fixed (map_zero D) r

/-- A nonzero locally nilpotent element has a last nonzero iterate. -/
theorem exists_last_nonzero_iterate (D : Derivation k A A) {a : A}
    (ha : a ≠ 0) (hnil : ∃ n : ℕ, (D : A → A)^[n] a = 0) :
    ∃ m : ℕ, (D : A → A)^[m] a ≠ 0 ∧ (D : A → A)^[m + 1] a = 0 := by
  classical
  have hn : Nat.find hnil ≠ 0 := by
    intro h
    have := Nat.find_spec hnil
    rw [h, Function.iterate_zero_apply] at this
    exact ha this
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨m, ?_, ?_⟩
  · exact Nat.find_min hnil (by omega)
  · simpa [hm] using Nat.find_spec hnil

/-- The only surviving term at the sum of the last possible derivative indices. -/
theorem derivation_iterate_top_mul (D : Derivation k A A) (a b : A) (m n : ℕ)
    (hm : (D : A → A)^[m + 1] a = 0)
    (hn : (D : A → A)^[n + 1] b = 0) :
    (D : A → A)^[m + n] (a * b) =
      (m + n).choose m • ((D : A → A)^[m] a * (D : A → A)^[n] b) := by
  rw [derivation_iterate_mul]
  apply sum_eq_single (m, n)
  · intro ij hij hne
    have hijsum := mem_antidiagonal.mp hij
    by_cases hi : m < ij.1
    · rw [derivation_iterate_eq_zero_of_le D hm (by omega), zero_mul, smul_zero]
    · have hj : n < ij.2 := by
        have hp : ij.1 ≠ m ∨ ij.2 ≠ n := by
          by_contra hp
          push Not at hp
          exact hne (Prod.ext hp.1 hp.2)
        omega
      rw [derivation_iterate_eq_zero_of_le D hn (by omega), mul_zero, smul_zero]
  · simp

/-- The kernel of a locally nilpotent derivation on a characteristic-zero domain
is factorially closed. This is `bun:factorial-closure` from the source. -/
theorem lnd_factorial_closure [IsDomain A] [CharZero A]
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) {a b : A}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : D (a * b) = 0) :
    D a = 0 ∧ D b = 0 := by
  obtain ⟨m, hm, hm'⟩ := exists_last_nonzero_iterate D ha (hD a)
  obtain ⟨n, hn, hn'⟩ := exists_last_nonzero_iterate D hb (hD b)
  have hmn : m + n = 0 := by
    by_contra hmn
    have hz : (D : A → A)^[m + n] (a * b) = 0 :=
      derivation_iterate_eq_zero_of_le D (m := 1) (by simpa using hab) (by omega)
    rw [derivation_iterate_top_mul D a b m n hm' hn', nsmul_eq_mul] at hz
    have hchoose : ((m + n).choose m : A) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : m ≤ m + n)).ne'
    exact (mul_ne_zero hchoose (mul_ne_zero hm hn)) hz
  obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hmn
  simpa using And.intro hm' hn'

/-- The difference-of-squares step of the rigidity proof: fixing
`a²u²-d²` forces the three factors `a`, `d`, and `u` to be fixed. -/
theorem lnd_fixed_of_difference_of_squares [IsDomain A] [CharZero A]
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) {a d u : A}
    (ha : a ≠ 0) (hu : u ≠ 0)
    (hminus : a * u - d ≠ 0) (hplus : a * u + d ≠ 0)
    (hv : D (a ^ 2 * u ^ 2 - d ^ 2) = 0) :
    D a = 0 ∧ D d = 0 ∧ D u = 0 := by
  have hprod : D ((a * u - d) * (a * u + d)) = 0 := by
    rw [show (a * u - d) * (a * u + d) = a ^ 2 * u ^ 2 - d ^ 2 by ring]
    exact hv
  obtain ⟨hm, hp⟩ := lnd_factorial_closure D hD hminus hplus hprod
  rw [map_sub] at hm
  rw [map_add] at hp
  have htwo : (2 : A) ≠ 0 := by norm_num
  have hau : D (a * u) = 0 := by
    apply (mul_eq_zero.mp (show (2 : A) * D (a * u) = 0 by
      calc
        (2 : A) * D (a * u) = (D (a * u) - D d) + (D (a * u) + D d) := by ring
        _ = 0 := by rw [hm, hp, add_zero])).resolve_left htwo
  have hd : D d = 0 := by simpa [hau] using hp
  obtain ⟨ha', hu'⟩ := lnd_factorial_closure D hD ha hu hau
  exact ⟨ha', hd, hu'⟩

end StableCoordinate

end OAI
