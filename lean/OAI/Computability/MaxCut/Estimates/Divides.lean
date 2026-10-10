import Mathlib
import OAI.Computability.MaxCut.Estimates.Rename

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem indicator_and (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1:ℕ) else 0)*(if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP,hQ]

def divides (a b : Expr) : Expr := .zero (remainder b a)
@[simp] theorem divides_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (divides a b).eval input args = if a.eval input args ∣ b.eval input args then 1 else 0 := by
  simp [divides, eval, Nat.dvd_iff_mod_eq_zero]

def prime (n : Expr) : Expr := .mul (le (.const 2) n)
  (.zero (.sum n (.mul (le (.const 2) (.arg 0)) (divides (.arg 0) (n.rename Nat.succ)))))

@[simp] theorem prime_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (prime n).eval input args = if (n.eval input args).Prime then 1 else 0 := by
  simp only [prime, eval, le_eval, divides_eval, rename_eval, bind]
  have h : (∑ i ∈ range (n.eval input args),
      (if 2 ≤ i then 1 else 0) * (if i ∣ n.eval input args then 1 else 0) : ℕ) = 0 ↔
      ∀ i, 2 ≤ i → i < n.eval input args → ¬ i ∣ n.eval input args := by
    rw [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    constructor
    · intro h i hi hn hd
      have hh := h i (mem_range.mpr hn)
      simp [hi, hd] at hh
    · intro h i hi
      by_cases h2 : 2 ≤ i
      · simp [h2, h i h2 (mem_range.mp hi)]
      · simp [h2]
  have hx : (if 2 ≤ n.eval input args then 1 else 0) *
      (if (∑ i ∈ range (n.eval input args),
        (if 2 ≤ i then 1 else 0)*(if i ∣ n.eval input args then 1 else 0) : ℕ)=0 then 1 else 0) =
        (if (n.eval input args).Prime then 1 else 0) := by
    simp only [h]
    exact (indicator_and _ _).trans (by simp only [Nat.prime_def_lt'])
  exact hx

def powTwo (n : Expr) : Expr := .mul (positive n)
  (.zero (.sum (.add n (.const 1))
    (.mul (prime (.arg 0)) (.mul (divides (.arg 0) (n.rename Nat.succ))
      (.zero (equal (.arg 0) (.const 2)))))))

@[simp] theorem powTwo_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (powTwo n).eval input args = if ∃ k : ℕ, n.eval input args = 2^k then 1 else 0 := by
  let N := n.eval input args
  have h : (∑ i ∈ range (N+1), (if i.Prime then 1 else 0)*
      ((if i ∣ N then 1 else 0)*(if (if i=2 then 1 else 0)=0 then 1 else 0)) : ℕ) = 0 ↔
      ∀ i ≤ N, i.Prime → i ∣ N → i=2 := by
    rw [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    constructor
    · intro h i hi hp hd
      have hh := h i (mem_range.mpr (by omega))
      by_contra hn
      simp [hp,hd,hn] at hh
    · intro h i hi
      by_cases hp : i.Prime <;> by_cases hd : i ∣ N <;> simp_all
      exact h i (by omega) hp hd
  have hh : (N ≠ 0 ∧ ∀ i ≤ N, i.Prime → i ∣ N → i=2) ↔ ∃ k : ℕ, N=2^k := by
    constructor
    · rintro ⟨hn,hp⟩
      exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn (fun {d} hd hdn => hp d (Nat.le_of_dvd (by omega) hdn) hd hdn)⟩
    · rintro ⟨k,hk⟩
      rw [hk]
      refine ⟨by positivity, ?_⟩
      intro i hi hp hd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
  simp only [powTwo, eval, positive_eval, prime_eval, divides_eval, equal_eval, rename_eval, bind]
  change (if N ≠ 0 then 1 else 0)*(if _=0 then 1 else 0) = if ∃ k, N=2^k then 1 else 0
  have hx : (if N ≠ 0 then 1 else 0)*(if
      (∑ i ∈ range (N+1), (if i.Prime then 1 else 0)*
      ((if i ∣ N then 1 else 0)*(if (if i=2 then 1 else 0)=0 then 1 else 0)) : ℕ) = 0
      then 1 else 0) = (if ∃ k, N=2^k then 1 else 0) := by
    simp only [h]
    exact (indicator_and _ _).trans (by simp only [hh])
  exact hx

/-- Cardinality of powers of two not exceeding an integer, hence its bit length. -/
def size (n : Expr) : Expr := .sum (.add n (.const 1)) (powTwo (.arg 0))

 theorem count_powers (N : ℕ) :
    (∑ i ∈ range (N+1), if ∃ k : ℕ, i=2^k then (1:ℕ) else 0) = N.size := by
  rw [sum_boole]
  have hb : {i ∈ range (N+1) | ∃ k : ℕ, i=2^k} = (range N.size).image (fun k => 2^k) := by
    ext i
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hi,k,rfl⟩
      exact ⟨k, Nat.lt_size.mpr (by omega), rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨by have := Nat.lt_size.mp hk; omega, k, rfl⟩
  rw [hb, card_image_of_injective _ (by intro a b h; exact (Nat.pow_right_injective (by omega : 2 ≤ 2)) h), card_range, Nat.cast_id]

@[simp] theorem size_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (size n).eval input args = (n.eval input args).size := by
  simp only [size, eval, powTwo_eval, bind]
  exact count_powers (n.eval input args)

/-- Locate the unique power of two having the requested binary digit index.
Search is bounded by n+1; no exponentially large unary number is ever built. -/
def digitPower (n i : Expr) : Expr := .sum (.add n (.const 1))
  (.mul (.arg 0) (.mul (powTwo (.arg 0))
    (equal (size (.arg 0)) (.add (i.rename Nat.succ) (.const 1)))))

 theorem digitPower_eval (n i : Expr) (input : List Bool) (args : ℕ → ℕ)
    (hi : i.eval input args < (n.eval input args).size) :
    (digitPower n i).eval input args = 2^(i.eval input args) := by
  simp only [digitPower, eval, powTwo_eval, size_eval, equal_eval, rename_eval, bind]
  let N := n.eval input args
  let I := i.eval input args
  have hpow : 2^I ∈ range (N+1) := mem_range.mpr (by have hh := Nat.lt_size.mp hi; change 2^I ≤ N at hh; omega)
  rw [sum_eq_single_of_mem (2^I) hpow]
  · simp [Nat.size_pow, I]
  · intro b hb hne
    by_cases hp : ∃ k : ℕ, b=2^k
    · obtain ⟨k,rfl⟩ := hp
      have hk : k ≠ I := by rintro rfl; exact hne rfl
      simp only [Nat.size_pow, Nat.add_right_cancel_iff]
      have hk' : k ≠ i.eval input (fun j => args j) := hk
      simp [hk']
    · simp [hp]

def digit (n i : Expr) : Expr := remainder (quotient n (digitPower n i)) (.const 2)

 theorem digit_eval (n i : Expr) (input : List Bool) (args : ℕ → ℕ)
    (hi : i.eval input args < (n.eval input args).size) :
    (digit n i).eval input args = n.eval input args / 2^(i.eval input args) % 2 := by
  simp [digit, eval, digitPower_eval n i input args hi]

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
