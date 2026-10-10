import Mathlib
import OAI.Computability.VertexCover.Fourier.Walsh

namespace OAI

                                                                                        

namespace UniqueGames.Foundations.PCP.CayleyTailCount

open scoped BigOperators
open UniqueGames.Foundations.Hastad (bitSign)

variable {α : Type*} [DecidableEq α]

def upperMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => 3 * m ≤ t.card

def lowerMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ m

def badMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  lowerMasks s m ∪ upperMasks s m

omit [DecidableEq α] in
                                                                     
theorem upperMasks_weight (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    (upperMasks s m).card * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by
  calc
    _ = ∑ _t ∈ upperMasks s m, 3 ^ (3 * m) := by simp
    _ ≤ ∑ t ∈ upperMasks s m, 3 ^ t.card := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.pow_le_pow_right (by decide) (Finset.mem_filter.mp ht).2
    _ ≤ ∑ t ∈ s.powerset, 3 ^ t.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro t _ _
        exact Nat.zero_le _
    _ = 4 ^ s.card := by
      simpa using Finset.sum_pow_mul_eq_add_pow (3 : ℕ) 1 s
    _ = 4 ^ (4 * m) := by rw [hcard]

theorem lowerMasks_complement_image (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).image (fun t => s \ t) = upperMasks s m := by
  ext u
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hts, htlo⟩ := Finset.mem_filter.mp ht
    have hsub := Finset.mem_powerset.mp hts
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  · intro hu
    obtain ⟨hus, huhi⟩ := Finset.mem_filter.mp hu
    have hsub := Finset.mem_powerset.mp hus
    apply Finset.mem_image.mpr
    refine ⟨s \ u, ?_, Finset.sdiff_sdiff_eq_self hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega

theorem lowerMasks_card_eq_upperMasks (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).card = (upperMasks s m).card := by
  have hinj : Set.InjOn (fun t : Finset α => s \ t) (lowerMasks s m) := by
    intro a ha b hb hab
    have has := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
    have hbs := Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1
    have h := congrArg (fun t : Finset α => s \ t) hab
    simpa only [Finset.sdiff_sdiff_eq_self has, Finset.sdiff_sdiff_eq_self hbs] using h
  calc
    _ = ((lowerMasks s m).image (fun t => s \ t)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = _ := congrArg Finset.card (lowerMasks_complement_image s m hcard)

private theorem ratio_le_of_weight («c» m : ℕ)
    (h : «c» * 3 ^ (3 * m) ≤ 4 ^ (4 * m)) :
    («c» : ℝ) / 2 ^ (4 * m) ≤ (16 / 27 : ℝ) ^ m := by
  have hc : («c» : ℝ) * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by exact_mod_cast h
  have h3 : 0 < (3 : ℝ) ^ (3 * m) := by positivity
  have h2 : 0 < (2 : ℝ) ^ (4 * m) := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ (4 * m) / 3 ^ (3 * m)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ h3).mpr hc) h2.le
    _ = _ := by
      rw [pow_mul, pow_mul, pow_mul, ← div_pow, ← div_pow]
      norm_num

omit [DecidableEq α] in
theorem upperMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((upperMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [hcard]
  exact ratio_le_of_weight _ m (upperMasks_weight s m hcard)

theorem lowerMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((lowerMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [lowerMasks_card_eq_upperMasks s m hcard]
  exact upperMasks_ratio_le s m hcard

theorem badMasks_ratio_le_sharp (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (16 / 27 : ℝ) ^ m := by
  have hc : ((badMasks s m).card : ℝ) ≤
      (lowerMasks s m).card + (upperMasks s m).card := by
    exact_mod_cast (Finset.card_union_le (lowerMasks s m) (upperMasks s m))
  have hpos : 0 < (2 : ℝ) ^ s.card := by positivity
  calc
    _ ≤ ((lowerMasks s m).card + (upperMasks s m).card : ℝ) / 2 ^ s.card :=
      div_le_div_of_nonneg_right hc hpos.le
    _ = ((lowerMasks s m).card : ℝ) / 2 ^ s.card +
        ((upperMasks s m).card : ℝ) / 2 ^ s.card := add_div _ _ _
    _ ≤ (16 / 27 : ℝ) ^ m + (16 / 27 : ℝ) ^ m :=
      add_le_add (lowerMasks_ratio_le s m hcard) (upperMasks_ratio_le s m hcard)
    _ = _ := by ring

theorem badMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (2 / 3 : ℝ) ^ m := by
  apply (badMasks_ratio_le_sharp s m hcard).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by norm_num)

section Words

variable {D : Type*} [Fintype D]

def trueMask (word : D → Bool) : Finset D :=
  Finset.univ.filter fun i => word i = true

def countTrue (word : D → Bool) : ℕ := (trueMask word).card

def badWord (m : ℕ) (word : D → Bool) : Prop :=
  countTrue word ≤ m ∨ 3 * m ≤ countTrue word

instance (m : ℕ) (word : D → Bool) : Decidable (badWord m word) :=
  inferInstanceAs (Decidable (countTrue word ≤ m ∨ 3 * m ≤ countTrue word))

theorem bitSign_mean_eq [Nonempty D] (word : D → Bool) :
    (𝔼 i, bitSign (word i)) =
      1 - 2 * ((countTrue word : ℝ) / Fintype.card D) := by
  have hsign (b : Bool) : bitSign b = 1 - 2 * (if b = true then (1 : ℝ) else 0) := by
    cases b <;> norm_num [bitSign]
  calc
    _ = (𝔼 i : D, (1 - 2 * (if word i = true then (1 : ℝ) else 0))) := by
      apply Finset.expect_congr rfl
      intro i _
      exact hsign (word i)
    _ = 1 - 2 * (𝔼 i, if word i = true then (1 : ℝ) else 0) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
      rfl

theorem not_badWord_bias (m : ℕ) (hcard : Fintype.card D = 4 * m) (hm : 0 < m)
    (word : D → Bool) (hword : ¬ badWord m word) :
    |𝔼 i, bitSign (word i)| ≤ (1 / 2 : ℝ) := by
  have hD : 0 < Fintype.card D := by rw [hcard]; omega
  let : Nonempty D := Fintype.card_pos_iff.mp hD
  have hlo : m < countTrue word := lt_of_not_ge (not_or.mp hword).1
  have hhi : countTrue word < 3 * m := lt_of_not_ge (not_or.mp hword).2
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlor : (m : ℝ) ≤ countTrue word := by exact_mod_cast hlo.le
  have hhir : (countTrue word : ℝ) ≤ 3 * m := by exact_mod_cast hhi.le
  have hden : 0 < 4 * (m : ℝ) := by positivity
  have hratioLo : (1 / 4 : ℝ) ≤ (countTrue word : ℝ) / (4 * m) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hratioHi : (countTrue word : ℝ) / (4 * m) ≤ (3 / 4 : ℝ) :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  rw [bitSign_mean_eq word, hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  apply abs_le.mpr
  constructor <;> linarith

def wordMaskEquiv [DecidableEq D] : (D → Bool) ≃ Finset D where
  toFun := trueMask
  invFun s i := decide (i ∈ s)
  left_inv word := by
    funext i
    cases h : word i <;> simp [trueMask, h]
  right_inv s := by
    ext i
    simp [trueMask]

theorem twoTail_probability [DecidableEq D] (m : ℕ) (hcard : Fintype.card D = 4 * m) :
    (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) ≤
      2 * (2 / 3 : ℝ) ^ m := by
  classical
  have he : (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) =
      (𝔼 s : Finset D, if s.card ≤ m ∨ 3 * m ≤ s.card then (1 : ℝ) else 0) := by
    apply Finset.expect_equiv (wordMaskEquiv (D := D))
    · intro word
      simp
    · intro word _
      rfl
  have hs : (Finset.univ.filter fun s : Finset D => s.card ≤ m ∨ 3 * m ≤ s.card) =
      badMasks (Finset.univ : Finset D) m := by
    ext s
    simp [badMasks, lowerMasks, upperMasks]
  rw [he, Fintype.expect_eq_sum_div_card, Finset.sum_boole, hs, Fintype.card_finset]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Finset.card_univ] using
    badMasks_ratio_le (Finset.univ : Finset D) m (by simpa using hcard)

end Words

theorem union_bound_le_half (n m : ℕ) (hm : 3 * (n + 2) ≤ m) :
    (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) ≤ 1 / 2 := by
  have hpow : (2 / 3 : ℝ) ^ m ≤ (2 / 3 : ℝ) ^ (3 * (n + 2)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbase : (2 / 3 : ℝ) ^ (3 * (n + 2)) ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) (n + 2)
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hpow.trans hbase) (by norm_num)) (by positivity)
    _ = 1 / 2 := by
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num

theorem fixed_parameters : 3 * (448 + 2) ≤ 16384 ∧ 4 * 16384 = 2 ^ 16 := by
  norm_num

theorem fixed_union_bound :
    (2 : ℝ) ^ 448 * (2 * (2 / 3 : ℝ) ^ 16384) ≤ 1 / 2 :=
  union_bound_le_half 448 16384 fixed_parameters.1

theorem seventh_power_size : (2 : ℕ) ^ 448 = (((2 : ℕ) ^ 16) ^ 7) ^ 4 := by
  rw [← pow_mul, ← pow_mul]

theorem seventh_power_abs_le {a : ℝ} (ha : |a| ≤ 1 / 2) : |a ^ 7| ≤ 1 / 128 := by
  rw [abs_pow]
  calc
    |a| ^ 7 ≤ (1 / 2 : ℝ) ^ 7 := pow_le_pow_left₀ (abs_nonneg a) ha 7
    _ = 1 / 128 := by norm_num

end UniqueGames.Foundations.PCP.CayleyTailCount

end OAI
