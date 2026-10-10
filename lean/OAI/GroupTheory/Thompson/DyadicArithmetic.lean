import OAI.GroupTheory.Thompson.Model
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Real dyadic arithmetic

Dyadic numbers are represented by an integer numerator and a nonnegative
power of two denominator. In particular, the grid denominator below is an
actual common denominator, not an assumption about the input finite set.
-/

universe uα

namespace ThompsonNonamenability

theorem isDyadic_div_pow (k : ℤ) (n : ℕ) :
    IsDyadic ((k : ℝ) / (2 : ℝ) ^ n) :=
  ⟨k, n, rfl⟩

theorem isDyadic_intCast (k : ℤ) : IsDyadic (k : ℝ) := by
  exact ⟨k, 0, by simp⟩

theorem isDyadic_natCast (k : ℕ) : IsDyadic (k : ℝ) := by
  simpa only [Int.cast_natCast] using isDyadic_intCast (k : ℤ)

@[simp] theorem isDyadic_zero : IsDyadic (0 : ℝ) := by
  simpa using isDyadic_intCast 0

@[simp] theorem isDyadic_one : IsDyadic (1 : ℝ) := by
  simpa using isDyadic_intCast 1

theorem IsDyadic.neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  rcases hx with ⟨k, n, rfl⟩
  exact ⟨-k, n, by simp only [Int.cast_neg, neg_div]⟩

theorem IsDyadic.mul {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) :
    IsDyadic (x * y) := by
  rcases hx with ⟨k, n, rfl⟩
  rcases hy with ⟨l, m, rfl⟩
  refine ⟨k * l, n + m, ?_⟩
  simp only [Int.cast_mul, pow_add, div_mul_div_comm]

theorem IsDyadic.add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) :
    IsDyadic (x + y) := by
  rcases hx with ⟨k, n, rfl⟩
  rcases hy with ⟨l, m, rfl⟩
  refine ⟨k * 2 ^ m + l * 2 ^ n, n + m, ?_⟩
  push_cast
  rw [pow_add]
  field_simp

theorem IsDyadic.sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) :
    IsDyadic (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem isDyadic_zpow (q : ℤ) : IsDyadic ((2 : ℝ) ^ q) := by
  cases q with
  | ofNat n =>
      simpa only [Int.ofNat_eq_natCast, zpow_natCast, Int.cast_pow, Int.cast_ofNat] using
        isDyadic_intCast ((2 : ℤ) ^ n)
  | negSucc n =>
      exact ⟨1, n + 1, by simp [zpow_negSucc, one_div]⟩

theorem IsDyadic.mul_zpow {x : ℝ} (hx : IsDyadic x) (q : ℤ) :
    IsDyadic (x * (2 : ℝ) ^ q) :=
  hx.mul (isDyadic_zpow q)

theorem IsDyadic.zpow_mul {x : ℝ} (hx : IsDyadic x) (q : ℤ) :
    IsDyadic ((2 : ℝ) ^ q * x) :=
  (isDyadic_zpow q).mul hx

theorem IsDyadic.div_zpow {x : ℝ} (hx : IsDyadic x) (q : ℤ) :
    IsDyadic (x / (2 : ℝ) ^ q) := by
  simpa only [div_eq_mul_inv, zpow_neg] using hx.mul_zpow (-q)

/-- Increasing a dyadic denominator does not change the represented number. -/
theorem dyadic_raise_denominator {x : ℝ} {n : ℕ}
    (hx : ∃ k : ℤ, x = (k : ℝ) / (2 : ℝ) ^ n) (m : ℕ) :
    ∃ k : ℤ, x = (k : ℝ) / (2 : ℝ) ^ (n + m) := by
  rcases hx with ⟨k, rfl⟩
  refine ⟨k * 2 ^ m, ?_⟩
  push_cast
  rw [pow_add]
  field_simp

theorem dyadic_denominator_mono {x : ℝ} {n N : ℕ}
    (hx : ∃ k : ℤ, x = (k : ℝ) / (2 : ℝ) ^ n) (hn : n ≤ N) :
    ∃ k : ℤ, x = (k : ℝ) / (2 : ℝ) ^ N := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact dyadic_raise_denominator hx m

/-- Every finite family of dyadic reals has a single power of two denominator. -/
theorem dyadic_common_denominator_finset {α : Type uα} (s : Finset α) (f : α → ℝ)
    (hs : ∀ a ∈ s, IsDyadic (f a)) :
    ∃ n : ℕ, ∀ a ∈ s, ∃ k : ℤ, f a = (k : ℝ) / (2 : ℝ) ^ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨k, n, hn⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨m, hm⟩ := ih (fun b hb => hs b (Finset.mem_insert_of_mem hb))
      refine ⟨n + m, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact dyadic_raise_denominator ⟨k, hn⟩ m
      · simpa only [Nat.add_comm m n] using dyadic_raise_denominator (hm b hb) n

theorem dyadic_common_denominator (s : Finset ℝ)
    (hs : ∀ x ∈ s, IsDyadic x) :
    ∃ n : ℕ, ∀ x ∈ s, ∃ k : ℤ, x = (k : ℝ) / (2 : ℝ) ^ n :=
  dyadic_common_denominator_finset s id hs

/-- A dyadic representation in the unit interval has a natural grid index. -/
theorem dyadic_nat_numerator {x : ℝ} {k : ℤ} {n : ℕ}
    (hx : x = (k : ℝ) / (2 : ℝ) ^ n) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∃ j : ℕ, j ≤ 2 ^ n ∧ x = (j : ℝ) / (2 : ℝ) ^ n := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hk0r : (0 : ℝ) ≤ (k : ℝ) := by
    have hh := (le_div_iff₀ hden).1 (hx ▸ h0)
    simpa only [zero_mul] using hh
  have hk0 : (0 : ℤ) ≤ k := by exact_mod_cast hk0r
  have hkr : (k : ℝ) ≤ (2 : ℝ) ^ n := (div_le_one hden).1 (hx ▸ h1)
  have hcast : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk0
  refine ⟨k.toNat, ?_, ?_⟩
  · have hj : (k.toNat : ℝ) ≤ (2 : ℝ) ^ n := by
      simpa only [hcast] using hkr
    exact_mod_cast hj
  · simpa only [hcast] using hx

theorem IsDyadic.exists_nat_grid {x : ℝ} (hx : IsDyadic x)
    (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∃ (n j : ℕ), j ≤ 2 ^ n ∧ x = (j : ℝ) / (2 : ℝ) ^ n := by
  obtain ⟨k, n, hk⟩ := hx
  obtain ⟨j, hj, hrepr⟩ := dyadic_nat_numerator hk h0 h1
  exact ⟨n, j, hj, hrepr⟩

/-- One grid simultaneously contains any given finite dyadic family in `[0,1]`. -/
theorem dyadic_common_nat_grid {α : Type uα} (s : Finset α) (f : α → ℝ)
    (hd : ∀ a ∈ s, IsDyadic (f a))
    (h0 : ∀ a ∈ s, 0 ≤ f a) (h1 : ∀ a ∈ s, f a ≤ 1) :
    ∃ n : ℕ, ∀ a ∈ s, ∃ j : ℕ, j ≤ 2 ^ n ∧ f a = (j : ℝ) / (2 : ℝ) ^ n := by
  obtain ⟨n, hn⟩ := dyadic_common_denominator_finset s f hd
  refine ⟨n, ?_⟩
  intro a ha
  obtain ⟨k, hk⟩ := hn a ha
  exact dyadic_nat_numerator hk (h0 a ha) (h1 a ha)

end ThompsonNonamenability

end OAI
