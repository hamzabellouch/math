import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

namespace OAI

/-! Reciprocal savings for one prime variable in a nondegenerate congruence. -/

namespace TwoPointCorrelations

open Finset

/-- A finite subset of one residue class has at most one exceptional initial
term; every subsequent reciprocal is bounded by a harmonic term divided by
the modulus. The set may consist only of primes or satisfy extra restrictions. -/
theorem reciprocal_congruence_sum (S : Finset ℕ) (H N p : ℕ)
    (hH : 0 < H) (hN : 1 ≤ N) (hp : 0 < p)
    (hlower : ∀ x ∈ S, H ≤ x) (hupper : ∀ x ∈ S, x ≤ N)
    (hcongruent : ∀ x ∈ S, ∀ y ∈ S, Nat.ModEq p x y) :
    ∑ x ∈ S, (x : ℝ)⁻¹ ≤ (H : ℝ)⁻¹ + (1 + Real.log N) / p := by
  classical
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    have ha : a ∈ S := min'_mem S hS
    let R := S.erase a
    let k : ℕ → ℕ := fun x => (x - a) / p
    have hkprod (x : ℕ) (hx : x ∈ R) : p * k x = x - a := by
      exact Nat.mul_div_cancel' ((hcongruent a ha x (mem_erase.mp hx).2).dvd')
    have hkpositive (x : ℕ) (hx : x ∈ R) : 0 < k x := by
      have hax := min'_le S x (mem_erase.mp hx).2
      have hne := (mem_erase.mp hx).1
      have hprod := hkprod x hx
      by_contra hn
      have hz : k x = 0 := by omega
      rw [hz, mul_zero] at hprod
      omega
    have hkupper (x : ℕ) (hx : x ∈ R) : k x ≤ N :=
      (Nat.div_le_self (x - a) p).trans ((Nat.sub_le x a).trans (hupper x (mem_erase.mp hx).2))
    have hkinj : Set.InjOn k R := by
      intro x hx y hy heq
      have hxprod := hkprod x hx
      have hyprod := hkprod y hy
      have hax := min'_le S x (mem_erase.mp hx).2
      have hay := min'_le S y (mem_erase.mp hy).2
      rw [heq] at hxprod
      omega
    have hweight (x : ℕ) (hx : x ∈ R) :
        (x : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ * (k x : ℝ)⁻¹ := by
      have hprod : (p : ℝ) * (k x : ℝ) ≤ x := by
        exact_mod_cast (show p * k x ≤ x by rw [hkprod x hx]; exact Nat.sub_le _ _)
      have hpos : 0 < (p : ℝ) * (k x : ℝ) := by
        exact mul_pos (by exact_mod_cast hp) (by exact_mod_cast hkpositive x hx)
      simpa only [mul_inv] using ((inv_le_inv₀ (lt_of_lt_of_le hpos hprod) hpos).mpr hprod)
    have hsubset : R.image k ⊆ Icc 1 N := by
      intro j hj
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
      exact mem_Icc.mpr ⟨hkpositive x hx, hkupper x hx⟩
    have hrest : ∑ x ∈ R, (x : ℝ)⁻¹ ≤ (1 + Real.log N) / p := by
      calc
        _ ≤ ∑ x ∈ R, (p : ℝ)⁻¹ * (k x : ℝ)⁻¹ := sum_le_sum hweight
        _ = ∑ j ∈ R.image k, (p : ℝ)⁻¹ * (j : ℝ)⁻¹ := by
          rw [sum_image hkinj]
        _ ≤ ∑ j ∈ Icc 1 N, (p : ℝ)⁻¹ * (j : ℝ)⁻¹ := by
          apply sum_le_sum_of_subset_of_nonneg hsubset
          intro j _ _
          positivity
        _ = (p : ℝ)⁻¹ * (harmonic N : ℝ) := by
          simp only [← mul_sum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        _ ≤ (p : ℝ)⁻¹ * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)
        _ = (1 + Real.log N) / p := by rw [div_eq_mul_inv]; ring
    have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
    have hHale : (H : ℝ) ≤ a := by exact_mod_cast hlower a ha
    have hfirst : (a : ℝ)⁻¹ ≤ (H : ℝ)⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le hHreal hHale) hHreal).mpr hHale
    calc
      _ = (a : ℝ)⁻¹ + ∑ x ∈ R, (x : ℝ)⁻¹ := by
        rw [← sum_erase_add S (fun x : ℕ => (x : ℝ)⁻¹) ha]
        simp only [R]
        ring
      _ ≤ _ := add_le_add hfirst hrest
  · have hzero : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp only [hzero, sum_empty]
    positivity

/-- A congruence with a nonzero coefficient modulo a prime admits only one
residue class, without any assumption that a larger matrix is invertible. -/
lemma congruence_same_residue {p x y : ℕ} (hp : p.Prime) {A B : ℤ}
    (hA : ¬(p : ℤ) ∣ A)
    (hx : (p : ℤ) ∣ A * x + B) (hy : (p : ℤ) ∣ A * y + B) :
    Nat.ModEq p x y := by
  have hprime : Prime (p : ℤ) := Int.prime_ofNat_iff.mpr hp
  have hdiff : (p : ℤ) ∣ A * ((y : ℤ) - x) := by
    convert hy.sub hx using 1
    ring
  exact Nat.modEq_iff_dvd.mpr ((hprime.dvd_mul.mp hdiff).resolve_left hA)

/-- The reciprocal saving used for each selected triangular relation. -/
theorem reciprocal_linear_congruence_sum (S : Finset ℕ) (H N p : ℕ) (A B : ℤ)
    (hH : 0 < H) (hN : 1 ≤ N) (hp : p.Prime) (hA : ¬(p : ℤ) ∣ A)
    (hlower : ∀ x ∈ S, H ≤ x) (hupper : ∀ x ∈ S, x ≤ N)
    (hcongruence : ∀ x ∈ S, (p : ℤ) ∣ A * x + B) :
    ∑ x ∈ S, (x : ℝ)⁻¹ ≤ (H : ℝ)⁻¹ + (1 + Real.log N) / p := by
  apply reciprocal_congruence_sum S H N p hH hN hp.pos hlower hupper
  intro x hx y hy
  exact congruence_same_residue hp hA (hcongruence x hx) (hcongruence y hy)

end TwoPointCorrelations

end OAI
