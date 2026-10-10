import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

namespace MarkovSuperreflexivity

theorem one_sub_pow_le_reciprocal_linear {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (m : ℕ) :
    (1 - a) ^ m ≤ 1 / (1 + (m : ℝ) * a) := by
  have hma : 0 ≤ (m : ℝ) * a := mul_nonneg (Nat.cast_nonneg m) ha0
  have hd : 0 < 1 + (m : ℝ) * a := by linarith
  have hb : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  apply (le_div_iff₀ hd).mpr
  calc
    (1 - a) ^ m * (1 + (m : ℝ) * a) ≤ (1 - a) ^ m * (1 + a) ^ m :=
      mul_le_mul_of_nonneg_left
        (one_add_mul_le_pow (by linarith : -2 ≤ a) m) (pow_nonneg hb m)
    _ = ((1 - a) * (1 + a)) ^ m := by rw [mul_pow]
    _ ≤ 1 := pow_le_one₀
      (mul_nonneg hb (by linarith : 0 ≤ 1 + a)) (by nlinarith [sq_nonneg a])

theorem le_inv_nat_of_half_le_one_sub_pow {a : ℝ} {m : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hm : 0 < m)
    (hhalf : (1 / 2 : ℝ) ≤ (1 - a) ^ m) :
    a ≤ 1 / (m : ℝ) := by
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hma : 0 ≤ (m : ℝ) * a := mul_nonneg hmreal.le ha0
  have hd : 0 < 1 + (m : ℝ) * a := by linarith
  have hrecip : (1 / 2 : ℝ) ≤ 1 / (1 + (m : ℝ) * a) :=
    hhalf.trans (one_sub_pow_le_reciprocal_linear ha0 ha1 m)
  have hcross := (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hd).mp hrecip
  apply (le_div_iff₀ hmreal).mpr
  nlinarith

theorem tail_bound_of_nat_scale_bound (Q : ℝ → ℝ) {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R)
    (hmono : AntitoneOn Q (Set.Ioi 0))
    (hQone : ∀ t : ℝ, 0 < t → Q t ≤ 1)
    (hscale : ∀ m : ℕ, 0 < m →
      Q (R * (m : ℝ) ^ (1 / p)) ≤ 1 / (m : ℝ)) :
    ∀ t : ℝ, 0 < t → Q t ≤ 2 * R ^ p / t ^ p := by
  intro t ht
  let x : ℝ := (t / R) ^ p
  have hxpos : 0 < x := Real.rpow_pos_of_pos (div_pos ht hR) p
  have hbound : Q t ≤ 2 / x := by
    by_cases hxone : 1 ≤ x
    · let m : ℕ := ⌊x⌋₊
      have hmpos : 0 < m := Nat.floor_pos.mpr hxone
      have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hmpos
      have hmone : (1 : ℝ) ≤ m := by
        exact_mod_cast (Nat.succ_le_of_lt hmpos)
      have hmle : (m : ℝ) ≤ x := Nat.floor_le hxpos.le
      have hlt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
      have htwom : x ≤ 2 * (m : ℝ) := by linarith
      have hroot : (m : ℝ) ^ (1 / p) ≤ t / R := by
        have hpow := Real.rpow_le_rpow (Nat.cast_nonneg m) hmle
          (le_of_lt (one_div_pos.mpr hp))
        simpa only [x, one_div, Real.rpow_rpow_inv (div_nonneg ht.le hR.le) hp.ne']
          using hpow
      have hthreshold : R * (m : ℝ) ^ (1 / p) ≤ t := by
        simpa only [mul_comm] using (le_div_iff₀ hR).mp hroot
      have hthreshold_pos : 0 < R * (m : ℝ) ^ (1 / p) :=
        mul_pos hR (Real.rpow_pos_of_pos hmreal _)
      have hrecip : 1 / (m : ℝ) ≤ 2 / x :=
        (div_le_div_iff₀ hmreal hxpos).mpr (by simpa only [one_mul] using htwom)
      exact ((hmono hthreshold_pos ht hthreshold).trans (hscale m hmpos)).trans hrecip
    · have hxlt : x < 1 := lt_of_not_ge hxone
      have hone : (1 : ℝ) ≤ 2 / x := (le_div_iff₀ hxpos).mpr (by linarith)
      exact (hQone t ht).trans hone
  calc
    Q t ≤ 2 / x := hbound
    _ = 2 * R ^ p / t ^ p := by
      dsimp only [x]
      rw [Real.div_rpow ht.le hR.le p, div_div_eq_mul_div]

theorem tail_bound_of_half_power_scale (Q : ℝ → ℝ) {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R)
    (hmono : AntitoneOn Q (Set.Ioi 0))
    (hQnonneg : ∀ t : ℝ, 0 < t → 0 ≤ Q t)
    (hQone : ∀ t : ℝ, 0 < t → Q t ≤ 1)
    (hscale : ∀ m : ℕ, 0 < m →
      (1 / 2 : ℝ) ≤ (1 - Q (R * (m : ℝ) ^ (1 / p))) ^ m) :
    ∀ t : ℝ, 0 < t → Q t ≤ 2 * R ^ p / t ^ p := by
  apply tail_bound_of_nat_scale_bound Q hp hR hmono hQone
  intro m hm
  have hthreshold_pos : 0 < R * (m : ℝ) ^ (1 / p) :=
    mul_pos hR (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _)
  exact le_inv_nat_of_half_le_one_sub_pow
    (hQnonneg _ hthreshold_pos) (hQone _ hthreshold_pos) hm (hscale m hm)

end MarkovSuperreflexivity

end OAI
