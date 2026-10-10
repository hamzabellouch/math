import OAI.NumberTheory.Ostmann.Preliminaries.PrimeDivisors
import OAI.NumberTheory.Ostmann.ZeroDensity.UnsignedPrimeMass

namespace OAI

/-! # A small weighted mass for the primes dividing one integer -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_log_weight_le_one (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 1 ≤ s) :
    Real.log p / (p : ℝ) ^ s ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow := Real.self_le_rpow_of_one_le hp1 hs
  have hpows : 0 < (p : ℝ) ^ s := Real.rpow_pos_of_pos hp0 _
  apply (div_le_one hpows).mpr
  have hlog := Real.log_le_sub_one_of_pos hp0
  linarith

/-- Splitting at the integer Y costs at most Y from small primes and
log(D)/Y from the remaining divisors. Taking Y near sqrt(log D) suffices
for the split-prime application. -/
theorem prime_divisor_mass_bound (P : Finset ℕ) (D Y : ℕ) (s : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hD : 0 < D) (hY : 0 < Y) (hs : 1 ≤ s) :
    (∑ p ∈ P.filter (fun p => p ∣ D), Real.log p / (p : ℝ) ^ s) ≤
      Y + Real.log D / Y := by
  let A := P.filter fun p => p ∣ D
  let U := A.filter fun p => p ≤ Y
  let V := A.filter fun p => ¬ p ≤ Y
  have hsplit : (∑ p ∈ A, Real.log p / (p : ℝ) ^ s) =
      (∑ p ∈ U, Real.log p / (p : ℝ) ^ s) + ∑ p ∈ V, Real.log p / (p : ℝ) ^ s := by
    exact (Finset.sum_filter_add_sum_filter_not A (fun p => p ≤ Y) _).symm
  have hUsub : U ⊆ Finset.Icc 1 Y := by
    intro p hp
    obtain ⟨hpA, hpY⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨(hP p (Finset.mem_filter.mp hpA).1).one_lt.le, hpY⟩
  have hUcard : U.card ≤ Y := by
    have hc := Finset.card_le_card hUsub
    simpa using hc
  have hUsum : (∑ p ∈ U, Real.log p / (p : ℝ) ^ s) ≤ Y := by
    calc
      _ ≤ ∑ p ∈ U, (1 : ℝ) := Finset.sum_le_sum (by
        intro p hp
        exact prime_log_weight_le_one p (hP p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1) s hs)
      _ = U.card := by simp
      _ ≤ Y := by exact_mod_cast hUcard
  have hVterm (p : ℕ) (hp : p ∈ V) : Real.log p / (p : ℝ) ^ s ≤ Real.log p / Y := by
    obtain ⟨hpA, hpY⟩ := Finset.mem_filter.mp hp
    have hprime := hP p (Finset.mem_filter.mp hpA).1
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
    have hpow := Real.self_le_rpow_of_one_le hp1 hs
    have hYp0 : (Y : ℝ) ≤ p := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hpY))
    have hYp : (Y : ℝ) ≤ (p : ℝ) ^ s := hYp0.trans hpow
    exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) (by exact_mod_cast hY) hYp
  have hVlog : (∑ p ∈ V, Real.log p) ≤ Real.log D :=
    sum_log_prime_divisors_le V hD
      (by intro p hp; exact hP p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
      (by intro p hp; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)
  have hVsum : (∑ p ∈ V, Real.log p / (p : ℝ) ^ s) ≤ Real.log D / Y := by
    calc
      _ ≤ ∑ p ∈ V, Real.log p / Y := Finset.sum_le_sum hVterm
      _ = (∑ p ∈ V, Real.log p) / Y := by rw [Finset.sum_div]
      _ ≤ Real.log D / Y := div_le_div_of_nonneg_right hVlog (Nat.cast_nonneg Y)
  change (∑ p ∈ A, Real.log p / (p : ℝ) ^ s) ≤ _
  rw [hsplit]
  exact add_le_add hUsum hVsum

end Ostmann

end OAI
