import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Group.Unbundled.Int

namespace OAI

/-!
# Primitive rational vectors

A denominator and an integer coordinate vector are primitive if they have no
common natural divisor greater than one. Multiplying such a vector by an integer
not divisible by its denominator leaves a nonintegral coordinate. Every such
coordinate stays at least the reciprocal denominator from every integer.
-/

universe uIndex

namespace QuantitativeVanDerWaerden

/-- The denominator and all coordinates have no nontrivial common divisor. -/
def PrimitiveVector {ι : Type uIndex} (h : ℕ) (t : ι → ℤ) : Prop :=
  ∀ e : ℕ, e ∣ h → (∀ i, (e : ℤ) ∣ t i) → e ≤ 1

/-- Changing coordinates by multiples of the denominator preserves primitivity. -/
theorem PrimitiveVector.of_congr {ι : Type uIndex} {h : ℕ} {T t : ι → ℤ}
    (hp : PrimitiveVector h T)
    (hcongr : ∀ i, ∃ z : ℤ, T i - t i = (h : ℤ) * z) :
    PrimitiveVector h t := by
  intro e he ht
  apply hp e he
  intro i
  obtain ⟨z, hz⟩ := hcongr i
  have heZ : (e : ℤ) ∣ (h : ℤ) := Int.natCast_dvd_natCast.mpr he
  have hdiff : (e : ℤ) ∣ T i - t i := by
    rw [hz]
    exact dvd_mul_of_dvd_left heZ z
  simpa only [sub_add_cancel] using dvd_add hdiff (ht i)

/-- Coordinates congruent to a common integer multiple of the first vector
do not add a new obstruction to its primitivity. -/
theorem PrimitiveVector.of_sum_congr_mul {ι : Type uIndex} {h : ℕ} {T S : ι → ℤ}
    (hp : PrimitiveVector h (Sum.elim T S)) (a : ℤ)
    (hcongr : ∀ i, ∃ z : ℤ, S i = a * T i + (h : ℤ) * z) :
    PrimitiveVector h T := by
  intro e he ht
  apply hp e he
  intro i
  cases i with
  | inl i => exact ht i
  | inr i =>
    obtain ⟨z, hz⟩ := hcongr i
    change (e : ℤ) ∣ S i
    rw [hz]
    exact dvd_add (dvd_mul_of_dvd_right (ht i) a)
      (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr he) z)

/-- Primitivity forces some multiplied coordinate to remain nonintegral. -/
theorem PrimitiveVector.exists_not_dvd_mul {ι : Type uIndex} [Fintype ι]
    {h : ℕ} {t : ι → ℤ} (hp : PrimitiveVector h t) (hh : 0 < h)
    {a : ℤ} (ha : ¬ (h : ℤ) ∣ a) : ∃ i, ¬ (h : ℤ) ∣ a * t i := by
  classical
  by_contra hnone
  have hall : ∀ i, (h : ℤ) ∣ a * t i := by simpa using hnone
  let g : ℕ := Finset.univ.gcd fun i => (t i).natAbs
  have hgle : Nat.gcd h g ≤ 1 := hp _ (Nat.gcd_dvd_left _ _) (by
    intro i
    exact Int.natCast_dvd.mpr ((Nat.gcd_dvd_right h g).trans
      (Finset.gcd_dvd (Finset.mem_univ i))))
  have hgpos : 0 < Nat.gcd h g := Nat.gcd_pos_of_pos_left g hh
  have hcop : Nat.Coprime h g := Nat.le_antisymm hgle hgpos
  have hmul : h ∣ a.natAbs * g := by
    have hg : h ∣ Finset.univ.gcd (fun i => a.natAbs * (t i).natAbs) := by
      apply Finset.dvd_gcd
      intro i _
      simpa only [Int.natAbs_mul] using (Int.natCast_dvd.mp (hall i))
    simpa only [Finset.gcd_mul_left, normalize_eq] using hg
  exact ha (Int.natCast_dvd.mpr (hcop.dvd_of_dvd_mul_right hmul))

/-- A nonintegral rational with denominator `h` is separated from every integer. -/
theorem rational_separation {h : ℕ} (hh : 0 < h) {b : ℤ}
    (hb : ¬ (h : ℤ) ∣ b) (z : ℤ) :
    1 / (h : ℝ) ≤ |(b : ℝ) / (h : ℝ) - (z : ℝ)| := by
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hn : b - (h : ℤ) * z ≠ 0 := by
    intro he
    exact hb ⟨z, sub_eq_zero.mp he⟩
  have habs : (1 : ℝ) ≤ |(b : ℝ) - (h : ℝ) * (z : ℝ)| := by
    simpa only [Int.cast_one, Int.cast_abs, Int.cast_sub,
      Int.cast_mul, Int.cast_natCast] using
      (Int.cast_mono (R := ℝ) (Int.one_le_abs hn))
  rw [div_sub' hhR.ne', abs_div, abs_of_pos hhR]
  exact div_le_div_of_nonneg_right habs hhR.le

/-- A primitive vector has a coordinate separated from every integer translate. -/
theorem PrimitiveVector.exists_separated_coordinate {ι : Type uIndex} [Fintype ι]
    {h : ℕ} {t : ι → ℤ} (hp : PrimitiveVector h t) (hh : 0 < h)
    {a : ℤ} (ha : ¬ (h : ℤ) ∣ a) :
    ∃ i, ∀ z : ℤ, 1 / (h : ℝ) ≤ |(a : ℝ) * (t i : ℝ) / h - z| := by
  obtain ⟨i, hi⟩ := hp.exists_not_dvd_mul hh ha
  refine ⟨i, fun z => ?_⟩
  simpa only [Int.cast_mul] using rational_separation hh hi z

end QuantitativeVanDerWaerden

end OAI
