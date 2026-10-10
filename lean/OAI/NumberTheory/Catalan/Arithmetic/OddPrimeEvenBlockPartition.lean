import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem evenBlock_quotient_parity {p z : ℕ}
    (hp : p % 2 = 1) (hz : z % 2 = 0) :
    (z / p) % 2 = (z % p) % 2 := by
  have he := congrArg (fun n : ℕ => n % 2) (Nat.mod_add_div z p)
  rw [Nat.add_mod, Nat.mul_mod, hp, one_mul, hz] at he
  simp only [Nat.mod_mod] at he
  omega

private theorem evenBlock_bounds {p a j : ℕ} (hp : p % 2 = 1)
    (hj : j < (p - 1) / 2 + 1) :
    (2 * a + 1) * p < 2 * (a + 1) * p - 2 * j ∧
      2 * (a + 1) * p - 2 * j ≤ 2 * (a + 1) * p := by
  have hjp : 2 * j < p := by omega
  have he : (2 * a + 1) * p + p = 2 * (a + 1) * p := by ring
  constructor <;> omega

private theorem evenBlock_survives {p a j : ℕ} (hp : p % 2 = 1)
    (hj : j < (p - 1) / 2 + 1) :
    0 < 2 * (a + 1) * p - 2 * j ∧
      (2 * (a + 1) * p - 2 * j) % 2 = 0 ∧
        ((2 * (a + 1) * p - 2 * j) % p = 0 ∨
          ((2 * (a + 1) * p - 2 * j) % p) % 2 = 1) := by
  have hb := evenBlock_bounds (a := a) hp hj
  have hmeven : (2 * (a + 1) * p) % 2 = 0 := by simp [Nat.mul_mod]
  have hjp : 2 * j < p := by omega
  refine ⟨by omega, by omega, ?_⟩
  by_cases hj0 : j = 0
  · left
    simp [hj0]
  · right
    have hr : p - 2 * j < p := by omega
    have he : (2 * a + 1) * p + p = 2 * (a + 1) * p := by ring
    have hz : 2 * (a + 1) * p - 2 * j =
        (2 * a + 1) * p + (p - 2 * j) := by omega
    have hmod : (2 * (a + 1) * p - 2 * j) % p = p - 2 * j := by
      rw [hz]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
    rw [hmod]
    omega

private theorem evenBlock_injective {p a b i j : ℕ} (hp : p % 2 = 1)
    (hi : i < (p - 1) / 2 + 1) (hj : j < (p - 1) / 2 + 1)
    (he : 2 * (a + 1) * p - 2 * i = 2 * (b + 1) * p - 2 * j) :
    a = b ∧ i = j := by
  have ha := evenBlock_bounds (a := a) hp hi
  have hb := evenBlock_bounds (a := b) hp hj
  have hab : a = b := by
    rcases lt_trichotomy a b with h | h | h
    · have hm := Nat.mul_le_mul_right p (show 2 * (a + 1) ≤ 2 * b + 1 by omega)
      omega
    · exact h
    · have hm := Nat.mul_le_mul_right p (show 2 * (b + 1) ≤ 2 * a + 1 by omega)
      omega
  subst b
  exact ⟨rfl, by omega⟩

private theorem evenBlock_preimage {p u z : ℕ} (hp : p % 2 = 1)
    (hu : u % 2 = 0) (hur : (u % p) % 2 = 0)
    (hz0 : 0 < z) (hzu : z ≤ u) (hz : z % 2 = 0)
    (hr : z % p = 0 ∨ (z % p) % 2 = 1) :
    ∃ a < (u / p) / 2, ∃ j < (p - 1) / 2 + 1,
      2 * (a + 1) * p - 2 * j = z := by
  have hp0 : 0 < p := by omega
  have huq : (u / p) % 2 = 0 := by
    rw [evenBlock_quotient_parity hp hu, hur]
  have hzq := evenBlock_quotient_parity hp hz
  have hquot : z / p ≤ u / p := Nat.div_le_div_right hzu
  have hdecomp : z % p + (z / p) * p = z := by
    simpa only [Nat.mul_comm p (z / p)] using Nat.mod_add_div z p
  rcases hr with hr0 | hr1
  · have hqe : (z / p) % 2 = 0 := by simpa [hr0] using hzq
    have hq0 : 0 < z / p := by
      by_cases hq : z / p = 0
      · simp [hr0, hq] at hdecomp
        omega
      · exact Nat.pos_of_ne_zero hq
    refine ⟨z / p / 2 - 1, by omega, 0, by omega, ?_⟩
    have ha : 2 * (z / p / 2 - 1 + 1) = z / p := by omega
    rw [ha]
    simp only [mul_zero, Nat.sub_zero]
    omega
  · have hqo : (z / p) % 2 = 1 := by omega
    have hrlt : z % p < p := Nat.mod_lt z hp0
    have hrpos : 0 < z % p := by omega
    refine ⟨z / p / 2, by omega, (p - z % p) / 2, by omega, ?_⟩
    have ha : 2 * (z / p / 2 + 1) = z / p + 1 := by omega
    have hj : 2 * ((p - z % p) / 2) = p - z % p := by omega
    rw [ha, hj, Nat.add_mul, one_mul]
    omega

theorem even_surviving_sum_eq_complete_blocks {β : Type*} [AddCommMonoid β]
    {p u : ℕ} (hp : p % 2 = 1) (hu : u % 2 = 0)
    (hur : (u % p) % 2 = 0) (f : ℕ → β) :
    (∑ z ∈ (Finset.range (u + 1)).filter
        (fun z => 0 < z ∧ z % 2 = 0 ∧ (z % p = 0 ∨ (z % p) % 2 = 1)), f z) =
      ∑ a ∈ Finset.range ((u / p) / 2),
        ∑ j ∈ Finset.range ((p - 1) / 2 + 1), f (2 * (a + 1) * p - 2 * j) := by
  classical
  have huq : (u / p) % 2 = 0 := by
    rw [evenBlock_quotient_parity hp hu, hur]
  rw [← Finset.sum_product (Finset.range ((u / p) / 2))
    (Finset.range ((p - 1) / 2 + 1))
    (fun x : ℕ × ℕ => f (2 * (x.1 + 1) * p - 2 * x.2))]
  symm
  refine Finset.sum_bij (fun x _ => 2 * (x.1 + 1) * p - 2 * x.2) ?_ ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_product.mp hx with ⟨ha, hj⟩
    have ha' := Finset.mem_range.mp ha
    have hj' := Finset.mem_range.mp hj
    have hm : 2 * (x.1 + 1) ≤ u / p := by omega
    have hmp := (Nat.mul_le_mul_right p hm).trans (Nat.div_mul_le_self u p)
    have hb := evenBlock_bounds (a := x.1) hp hj'
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      evenBlock_survives (a := x.1) hp hj'⟩
  · intro x hx y hy he
    have hjx := Finset.mem_range.mp (Finset.mem_product.mp hx).2
    have hjy := Finset.mem_range.mp (Finset.mem_product.mp hy).2
    have hxy := evenBlock_injective hp hjx hjy he
    exact Prod.ext hxy.1 hxy.2
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzu, hz0, hzEven, hr⟩
    obtain ⟨a, ha, j, hj, he⟩ := evenBlock_preimage hp hu hur hz0
      (by have := Finset.mem_range.mp hzu; omega) hzEven hr
    refine ⟨(a, j), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hj⟩, he⟩
  · intro x hx
    rfl

end InternalCatalan

end OAI
