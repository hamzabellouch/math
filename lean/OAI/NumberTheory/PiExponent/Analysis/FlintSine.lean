import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import OAI.NumberTheory.PiExponent.Analysis.FlintHills

namespace OAI

namespace PiExponent

theorem sin_nat_ne_zero {n : ℕ} (hn : 0 < n) : Real.sin (n : ℝ) ≠ 0 := by
  rw [Real.sin_ne_zero_iff]
  intro k
  by_cases hk : k = 0
  · simpa only [hk, Int.cast_zero, zero_mul, ne_eq, eq_comm, Nat.cast_eq_zero] using hn.ne'
  · simpa only [Int.cast_natCast] using (irrational_pi.intCast_mul hk).ne_int (n : ℤ)

noncomputable def sineGroup (n : ℕ) : ℕ := (round ((n : ℝ) / Real.pi)).toNat

theorem round_div_pi_nonneg (n : ℕ) : 0 ≤ round ((n : ℝ) / Real.pi) := by
  have h := sub_half_lt_round ((n : ℝ) / Real.pi)
  have hn : (0 : ℝ) ≤ (n : ℝ) / Real.pi := by positivity
  have hh : (-1 : ℝ) < (round ((n : ℝ) / Real.pi) : ℝ) := by linarith
  have : (-1 : ℤ) < round ((n : ℝ) / Real.pi) := by exact_mod_cast hh
  omega

theorem sineGroup_cast (n : ℕ) : (sineGroup n : ℝ) = round ((n : ℝ) / Real.pi) := by
  unfold sineGroup
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (round_div_pi_nonneg n)]

theorem sineGroup_distance (n : ℕ) :
    |(n : ℝ) - sineGroup n * Real.pi| ≤ Real.pi / 2 := by
  have hh := mul_le_mul_of_nonneg_right (abs_sub_round ((n : ℝ) / Real.pi)) Real.pi_pos.le
  rw [sineGroup_cast]
  calc
    |(n : ℝ) - (round ((n : ℝ) / Real.pi) : ℝ) * Real.pi| =
        |(n : ℝ) / Real.pi - (round ((n : ℝ) / Real.pi) : ℝ)| * Real.pi := by
      calc
        _ = |((n : ℝ) / Real.pi - (round ((n : ℝ) / Real.pi) : ℝ)) * Real.pi| := by
          congr 1
          field_simp
        _ = _ := by rw [abs_mul, abs_of_pos Real.pi_pos]
    _ ≤ Real.pi / 2 := by linarith

theorem sineGroup_pos {n : ℕ} (hn : 2 ≤ n) : 0 < sineGroup n := by
  have hh := sineGroup_distance n
  have hlow := (abs_le.mp hh).2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  by_contra h
  have hz : sineGroup n = 0 := Nat.eq_zero_of_not_pos h
  rw [hz] at hlow
  norm_num at hlow
  linarith [Real.pi_lt_four]

theorem sineGroup_lower {n : ℕ} (hn : 2 ≤ n) :
    Real.pi * (sineGroup n : ℝ) / 2 ≤ n := by
  have hh := (abs_le.mp (sineGroup_distance n)).1
  have hq : (1 : ℝ) ≤ sineGroup n := by exact_mod_cast sineGroup_pos hn
  nlinarith [Real.pi_pos]

theorem abs_sin_lower_integerDistance (n : ℕ) :
    (2 / Real.pi) * integerDistance (sineGroup n * Real.pi) ≤ |Real.sin n| := by
  have hs := Real.mul_abs_le_abs_sin (sineGroup_distance n)
  have hd := integerDistance_le (sineGroup n * Real.pi) (n : ℤ)
  have heq : |Real.sin ((n : ℝ) - (sineGroup n : ℝ) * Real.pi)| = |Real.sin n| := by
    rw [Real.sin_sub_nat_mul_pi, abs_mul, abs_pow]
    norm_num
  rw [heq] at hs
  have : integerDistance (sineGroup n * Real.pi) ≤ |(n : ℝ) - sineGroup n * Real.pi| := by
    simpa only [Int.cast_natCast, abs_sub_comm] using hd
  exact (mul_le_mul_of_nonneg_left this (by positivity)).trans hs

theorem sineGroup_residue_injective : Function.Injective
    (fun n : ℕ => (sineGroup n, (⟨n % 4, Nat.mod_lt n (by decide)⟩ : Fin 4))) := by
  intro a b hab
  have hg : sineGroup a = sineGroup b := congrArg Prod.fst hab
  have hm : a % 4 = b % 4 := congrArg (fun x : ℕ × Fin 4 => (x.2 : ℕ)) hab
  have ha := abs_le.mp (sineGroup_distance a)
  have hb := abs_le.mp (sineGroup_distance b)
  rw [hg] at ha
  have habR : (a : ℝ) - b < 4 := by linarith [Real.pi_lt_four]
  have hbaR : (b : ℝ) - a < 4 := by linarith [Real.pi_lt_four]
  have habN : a < b + 4 := by exact_mod_cast (show (a : ℝ) < b + 4 by linarith)
  have hbaN : b < a + 4 := by exact_mod_cast (show (b : ℝ) < a + 4 by linarith)
  omega

theorem flint_term_le_distance_term {n : ℕ} (hn : 2 ≤ n) :
    1 / ((n : ℝ) ^ 3 * Real.sin n ^ 2) ≤
      4 / ((sineGroup n : ℝ) ^ 3 * integerDistance (sineGroup n * Real.pi) ^ 2) := by
  have hqN := sineGroup_pos hn
  have hq : (0 : ℝ) < sineGroup n := by exact_mod_cast hqN
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd := integerDistance_mul_pos irrational_pi hqN
  have hd0 := hd.le
  have hs0 := abs_nonneg (Real.sin n)
  have hlow := abs_sin_lower_integerDistance n
  have h2 : integerDistance (sineGroup n * Real.pi) ≤ 2 * |Real.sin n| := by
    have hp : 0 < Real.pi := Real.pi_pos
    have hm := (div_le_iff₀ hp).mp (show
        2 * integerDistance (sineGroup n * Real.pi) / Real.pi ≤ |Real.sin n| by
      simpa only [div_mul_eq_mul_div] using hlow)
    nlinarith [Real.pi_lt_four]
  have hs : 0 < Real.sin n ^ 2 := by
    have : Real.sin n ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero, mul_zero] at h2
      linarith
    exact sq_pos_of_ne_zero this
  have hqle : (sineGroup n : ℝ) ≤ n := by
    have h := sineGroup_lower hn
    nlinarith [Real.pi_gt_three]
  have hcube := pow_le_pow_left₀ hq.le hqle 3
  have hd2 : integerDistance (sineGroup n * Real.pi) ^ 2 ≤ 4 * Real.sin n ^ 2 := by
    nlinarith [sq_abs (Real.sin n), sq_nonneg (2 * |Real.sin n| -
      integerDistance (sineGroup n * Real.pi))]
  have hp : (sineGroup n : ℝ) ^ 3 * integerDistance (sineGroup n * Real.pi) ^ 2 ≤
      4 * ((n : ℝ) ^ 3 * Real.sin n ^ 2) := by
    calc
      _ ≤ (sineGroup n : ℝ) ^ 3 * (4 * Real.sin n ^ 2) :=
        mul_le_mul_of_nonneg_left hd2 (by positivity)
      _ ≤ (n : ℝ) ^ 3 * (4 * Real.sin n ^ 2) :=
        mul_le_mul_of_nonneg_right hcube (by positivity)
      _ = _ := by ring
  exact (div_le_div_iff₀ (mul_pos (pow_pos hnR 3) hs)
    (mul_pos (pow_pos hq 3) (sq_pos_of_pos hd))).mpr (by simpa using hp)

theorem summable_sineGroup_comp {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hf : Summable f) : Summable (fun n => f (sineGroup n)) := by
  have hp : Summable (fun p : ℕ × Fin 4 => f p.1) := by
    apply (summable_prod_of_nonneg (fun p => hf0 p.1)).mpr
    constructor
    · intro n
      exact Summable.of_finite
    · simpa using hf.mul_left 4
  exact hp.comp_injective sineGroup_residue_injective

theorem flintHills_summable_of_distance_summable
    (h : Summable (fun q : ℕ =>
      1 / ((q : ℝ) ^ 3 * integerDistance (q * Real.pi) ^ 2))) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 3 * Real.sin n ^ 2)) := by
  have hh : Summable (fun q : ℕ =>
      4 / ((q : ℝ) ^ 3 * integerDistance (q * Real.pi) ^ 2)) := by
    simpa only [mul_one_div] using h.mul_left 4
  have hcomp := summable_sineGroup_comp (fun q => by positivity) hh
  have htail := (summable_nat_add_iff 2).mpr hcomp
  apply (summable_nat_add_iff 2).mp
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => flint_term_le_distance_term (show 2 ≤ n + 2 by omega)) htail

theorem flintHills_positive_summable_of_distance_summable
    (h : Summable (fun q : ℕ =>
      1 / ((q : ℝ) ^ 3 * integerDistance (q * Real.pi) ^ 2))) :
    Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 3 * Real.sin (n + 1 : ℕ) ^ 2)) :=
  (summable_nat_add_iff 1).mpr (flintHills_summable_of_distance_summable h)

end PiExponent

end OAI
