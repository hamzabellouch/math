import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLoss
import OAI.NumberTheory.Catalan.Determinants.TwoAdicSmoothedMinor

namespace OAI


noncomputable section

namespace InternalCatalan

def oddLowerPairProfile (x : ℝ) : ℝ :=
  max (min (min x (59 - x)) 19 - max 7 (65 - 2 * x)) 0

def oddLowerLossProfile (x : ℝ) : ℝ :=
  96 - max (oddLowerPairProfile x - 4) 0

def oddUpperRankProfile (x : ℝ) : ℝ :=
  max (59 - x) 0 + max (59 - x - 19) 0 +
    max (65 - x - max 7 (59 - x)) 0

def oddUpperSimpleProfile (x : ℝ) : ℝ :=
  max (min 19 (59 - x) - 7) 0 +
    max (min 7 (65 - x) - max 0 (59 - x)) 0

def oddUpperLossProfile (x : ℝ) : ℝ :=
  min (min 96 (48 + oddUpperRankProfile x))
    (2 * oddUpperRankProfile x + oddUpperSimpleProfile x)

def oddLowerPairCountReal (N : ℕ) (p : ℝ) : ℝ :=
  max (min (min p ((L N : ℝ) - p)) (A N : ℝ) -
    max (b N : ℝ) ((H N : ℝ) - 2 * p)) 0

def oddLowerCountLossReal (N : ℕ) (p : ℝ) : ℝ :=
  2 * (n N : ℝ) - max (oddLowerPairCountReal N p - (q N : ℝ)) 0

def oddUpperRankCountReal (N : ℕ) (p : ℝ) : ℝ :=
  max ((L N : ℝ) - p) 0 + max ((L N : ℝ) - p - (A N : ℝ)) 0 +
    max ((H N : ℝ) - p - max (b N : ℝ) ((L N : ℝ) - p)) 0

def oddUpperSimpleCountReal (N : ℕ) (p : ℝ) : ℝ :=
  max (min (A N : ℝ) ((L N : ℝ) - p) - (b N : ℝ)) 0 +
    max (min (b N : ℝ) ((H N : ℝ) - p) - max 0 ((L N : ℝ) - p)) 0

def oddUpperCountLossReal (N : ℕ) (p : ℝ) : ℝ :=
  min (min (2 * (n N : ℝ)) ((n N : ℝ) + oddUpperRankCountReal N p))
    (2 * oddUpperRankCountReal N p + oddUpperSimpleCountReal N p)

def oddLowerPairCount (N p : ℕ) : ℕ :=
  (min (min (p : ℤ) ((L N : ℤ) - p)) (A N : ℤ) -
    max (b N : ℤ) ((H N : ℤ) - 2 * p)).toNat

def oddLowerCountLoss (N p : ℕ) : ℕ :=
  2 * n N - (oddLowerPairCount N p - q N)

def oddUpperRankCount (N p : ℕ) : ℕ :=
  ((L N : ℤ) - p).toNat + ((L N : ℤ) - p - (A N : ℤ)).toNat +
    ((H N : ℤ) - p - max (b N : ℤ) ((L N : ℤ) - p)).toNat

def oddUpperSimpleCount (N p : ℕ) : ℕ :=
  (min (A N : ℤ) ((L N : ℤ) - p) - (b N : ℤ)).toNat +
    (min (b N : ℤ) ((H N : ℤ) - p) - max 0 ((L N : ℤ) - p)).toNat

def oddUpperCountLoss (N p : ℕ) : ℕ :=
  min (min (2 * n N) (n N + oddUpperRankCount N p))
    (2 * oddUpperRankCount N p + oddUpperSimpleCount N p)







theorem oddLoss_intToNat_cast (z : ℤ) :
    (z.toNat : ℝ) = max (z : ℝ) 0 := by
  by_cases hz : 0 ≤ z
  · have hzR : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    rw [max_eq_left hzR]
    exact_mod_cast (Int.toNat_of_nonneg hz)
  · have hzle : z ≤ 0 := by omega
    have hzR : (z : ℝ) ≤ 0 := by exact_mod_cast hzle
    rw [Int.toNat_eq_zero.mpr hzle, Nat.cast_zero, max_eq_right hzR]

theorem oddLoss_natSub_cast (a b : ℕ) :
    ((a - b : ℕ) : ℝ) = max ((a : ℝ) - (b : ℝ)) 0 := by
  by_cases hab : b ≤ a
  · have habR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hab
    rw [Nat.cast_sub hab, max_eq_left (sub_nonneg.mpr habR)]
  · have hba : a ≤ b := by omega
    have hbaR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hba
    rw [Nat.sub_eq_zero_of_le hba, Nat.cast_zero,
      max_eq_right (sub_nonpos.mpr hbaR)]

theorem oddLoss_intCast_min (a b : ℤ) :
    ((min a b : ℤ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  rcases le_total a b with hab | hba
  · have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [min_eq_left hab, min_eq_left habR]
  · have hbaR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    rw [min_eq_right hba, min_eq_right hbaR]

theorem oddLoss_intCast_max (a b : ℤ) :
    ((max a b : ℤ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  rcases le_total a b with hab | hba
  · have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [max_eq_right hab, max_eq_right habR]
  · have hbaR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    rw [max_eq_left hba, max_eq_left hbaR]

theorem oddLoss_natCast_min (a b : ℕ) :
    ((min a b : ℕ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  rcases le_total a b with hab | hba
  · have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [min_eq_left hab, min_eq_left habR]
  · have hbaR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    rw [min_eq_right hba, min_eq_right hbaR]

theorem oddLowerPairCount_cast (N p : ℕ) :
    (oddLowerPairCount N p : ℝ) = oddLowerPairCountReal N (p : ℝ) := by
  simp only [oddLowerPairCount, oddLowerPairCountReal, oddLoss_intToNat_cast,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
    oddLoss_intCast_min, oddLoss_intCast_max]

theorem oddUpperRankCount_cast (N p : ℕ) :
    (oddUpperRankCount N p : ℝ) = oddUpperRankCountReal N (p : ℝ) := by
  simp only [oddUpperRankCount, oddUpperRankCountReal, Nat.cast_add,
    oddLoss_intToNat_cast, Int.cast_sub, Int.cast_natCast, oddLoss_intCast_max]

theorem oddUpperSimpleCount_cast (N p : ℕ) :
    (oddUpperSimpleCount N p : ℝ) = oddUpperSimpleCountReal N (p : ℝ) := by
  simp only [oddUpperSimpleCount, oddUpperSimpleCountReal, Nat.cast_add,
    oddLoss_intToNat_cast, Int.cast_sub, Int.cast_natCast, Int.cast_zero,
    oddLoss_intCast_min, oddLoss_intCast_max]

theorem oddUpperCountLoss_cast (N p : ℕ) :
    (oddUpperCountLoss N p : ℝ) = oddUpperCountLossReal N (p : ℝ) := by
  simp only [oddUpperCountLoss, oddUpperCountLossReal, oddLoss_natCast_min,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    oddUpperRankCount_cast, oddUpperSimpleCount_cast]

theorem oddLowerPairCount_le_A (N p : ℕ) : oddLowerPairCount N p ≤ A N := by
  unfold oddLowerPairCount
  rw [Int.toNat_le]
  have htop : min (min (p : ℤ) ((L N : ℤ) - p)) (A N : ℤ) ≤ A N :=
    min_le_right _ _
  have hbottom : (0 : ℤ) ≤ max (b N : ℤ) ((H N : ℤ) - 2 * p) :=
    le_trans (Int.natCast_nonneg (b N)) (le_max_left _ _)
  omega

theorem oddLowerLossSubtrahend_le (N p : ℕ) :
    oddLowerPairCount N p - q N ≤ 2 * n N := by
  have hpair := oddLowerPairCount_le_A N p
  have hsub : oddLowerPairCount N p - q N ≤ oddLowerPairCount N p :=
    Nat.sub_le _ _
  have hA : A N ≤ 2 * n N := by
    unfold A n
    omega
  exact le_trans hsub (le_trans hpair hA)

theorem oddLowerCountLoss_cast (N p : ℕ) :
    (oddLowerCountLoss N p : ℝ) = oddLowerCountLossReal N (p : ℝ) := by
  unfold oddLowerCountLoss oddLowerCountLossReal
  rw [Nat.cast_sub (oddLowerLossSubtrahend_le N p),
    oddLoss_natSub_cast, oddLowerPairCount_cast]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

end InternalCatalan

end



namespace InternalCatalan

theorem oddLowerPairProfile_of_le_23 (x : ℝ) (hx : x ≤ 23) :
    oddLowerPairProfile x = 0 := by
  unfold oddLowerPairProfile
  apply max_eq_right
  apply sub_nonpos.mpr
  calc
    min (min x (59 - x)) 19 ≤ 19 := min_le_right _ _
    _ ≤ 65 - 2 * x := by linarith
    _ ≤ max 7 (65 - 2 * x) := le_max_right _ _

theorem oddLowerPairProfile_23_29 (x : ℝ) (hlo : 23 ≤ x) (hhi : x ≤ 29) :
    oddLowerPairProfile x = 2 * x - 46 := by
  have hmin : min (min x (59 - x)) 19 = 19 :=
    min_eq_right (le_min (by linarith) (by linarith))
  rw [oddLowerPairProfile, hmin,
    max_eq_right (show (7 : ℝ) ≤ 65 - 2 * x by linarith),
    max_eq_left (show (0 : ℝ) ≤ 19 - (65 - 2 * x) by linarith)]
  ring

theorem oddLowerPairProfile_29_65div2 (x : ℝ)
    (hlo : 29 ≤ x) (hhi : x ≤ 65 / 2) :
    oddLowerPairProfile x = 12 := by
  have hmin : min (min x (59 - x)) 19 = 19 :=
    min_eq_right (le_min (by linarith) (by linarith))
  rw [oddLowerPairProfile, hmin,
    max_eq_left (show (65 : ℝ) - 2 * x ≤ 7 by linarith)]
  norm_num

theorem oddLowerLossProfile_eq (x : ℝ) (hx : x ≤ 65 / 2) :
    oddLowerLossProfile x = oddPrimeLoss x := by
  by_cases h23 : x ≤ 23
  · rw [oddLowerLossProfile, oddLowerPairProfile_of_le_23 x h23,
      oddPrimeLoss_of_le_25 x (by linarith)]
    norm_num
  by_cases h25 : x ≤ 25
  · rw [oddLowerLossProfile, oddLowerPairProfile_23_29 x (by linarith) (by linarith),
      max_eq_right (show 2 * x - 46 - 4 ≤ (0 : ℝ) by linarith),
      oddPrimeLoss_of_le_25 x h25]
    ring
  by_cases h29 : x ≤ 29
  · rw [oddLowerLossProfile, oddLowerPairProfile_23_29 x (by linarith) h29,
      max_eq_left (show (0 : ℝ) ≤ 2 * x - 46 - 4 by linarith),
      oddPrimeLoss_25_29 x (by linarith) h29]
    ring
  rw [oddLowerLossProfile, oddLowerPairProfile_29_65div2 x (by linarith) hx,
    oddPrimeLoss_29_65div2 x (by linarith) hx]
  norm_num

end InternalCatalan



noncomputable section

namespace InternalCatalan

theorem oddUpperProfiles_65div2_40 (x : ℝ) (hlo : 65 / 2 ≤ x) (hhi : x ≤ 40) :
    oddUpperRankProfile x = 105 - 2 * x ∧ oddUpperSimpleProfile x = 12 := by
  have _ := hlo
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_left (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 59 - x - 19 by linarith),
      max_eq_right (show (7 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 65 - x - (59 - x) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_left (show (19 : ℝ) ≤ 59 - x by linarith),
      min_eq_left (show (7 : ℝ) ≤ 65 - x by linarith),
      max_eq_right (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 19 - 7 by norm_num),
      max_eq_right (show (7 : ℝ) - (59 - x) ≤ 0 by linarith)]
    ring

theorem oddUpperProfiles_40_52 (x : ℝ) (hlo : 40 ≤ x) (hhi : x ≤ 52) :
    oddUpperRankProfile x = 65 - x ∧ oddUpperSimpleProfile x = 52 - x := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_left (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_right (show (7 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 65 - x - (59 - x) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_left (show (7 : ℝ) ≤ 65 - x by linarith),
      max_eq_right (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_left (show (0 : ℝ) ≤ 59 - x - 7 by linarith),
      max_eq_right (show (7 : ℝ) - (59 - x) ≤ 0 by linarith)]
    ring

theorem oddUpperProfiles_52_58 (x : ℝ) (hlo : 52 ≤ x) (hhi : x ≤ 58) :
    oddUpperRankProfile x = 117 - 2 * x ∧ oddUpperSimpleProfile x = x - 52 := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_left (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (7 : ℝ) by linarith),
      max_eq_left (show (0 : ℝ) ≤ 65 - x - 7 by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_left (show (7 : ℝ) ≤ 65 - x by linarith),
      max_eq_right (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 7 ≤ (0 : ℝ) by linarith),
      max_eq_left (show (0 : ℝ) ≤ 7 - (59 - x) by linarith)]
    ring

theorem oddUpperProfiles_58_59 (x : ℝ) (hlo : 58 ≤ x) (hhi : x ≤ 59) :
    oddUpperRankProfile x = 59 - x ∧ oddUpperSimpleProfile x = 6 := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_left (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (7 : ℝ) by linarith),
      max_eq_right (show 65 - x - 7 ≤ (0 : ℝ) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_right (show 65 - x ≤ (7 : ℝ) by linarith),
      max_eq_right (show (0 : ℝ) ≤ 59 - x by linarith),
      max_eq_right (show 59 - x - 7 ≤ (0 : ℝ) by linarith),
      max_eq_left (show (0 : ℝ) ≤ 65 - x - (59 - x) by linarith)]
    ring

theorem oddUpperProfiles_59_65 (x : ℝ) (hlo : 59 ≤ x) (hhi : x ≤ 65) :
    oddUpperRankProfile x = 0 ∧ oddUpperSimpleProfile x = 65 - x := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_right (show 59 - x ≤ (0 : ℝ) by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (7 : ℝ) by linarith),
      max_eq_right (show 65 - x - 7 ≤ (0 : ℝ) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_right (show 65 - x ≤ (7 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (0 : ℝ) by linarith),
      max_eq_right (show 59 - x - 7 ≤ (0 : ℝ) by linarith),
      sub_zero, max_eq_left (show (0 : ℝ) ≤ 65 - x by linarith)]
    ring

theorem oddUpperProfiles_of_ge_65 (x : ℝ) (hlo : 65 ≤ x) :
    oddUpperRankProfile x = 0 ∧ oddUpperSimpleProfile x = 0 := by
  constructor
  · simp only [oddUpperRankProfile,
      max_eq_right (show 59 - x ≤ (0 : ℝ) by linarith),
      max_eq_right (show 59 - x - 19 ≤ (0 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (7 : ℝ) by linarith),
      max_eq_right (show 65 - x - 7 ≤ (0 : ℝ) by linarith)]
    ring
  · simp only [oddUpperSimpleProfile,
      min_eq_right (show 59 - x ≤ (19 : ℝ) by linarith),
      min_eq_right (show 65 - x ≤ (7 : ℝ) by linarith),
      max_eq_left (show 59 - x ≤ (0 : ℝ) by linarith),
      max_eq_right (show 59 - x - 7 ≤ (0 : ℝ) by linarith),
      sub_zero, max_eq_right (show 65 - x ≤ (0 : ℝ) by linarith)]
    ring

private theorem oddUpperLossProfile_of_second (x r s : ℝ)
    (hR : oddUpperRankProfile x = r) (hS : oddUpperSimpleProfile x = s)
    (h96 : 2 * r + s ≤ 96) (h48 : 2 * r + s ≤ 48 + r) :
    oddUpperLossProfile x = 2 * r + s := by
  rw [oddUpperLossProfile, hR, hS, min_eq_right (le_min h96 h48)]

theorem oddUpperLossProfile_eq (x : ℝ) (hx : 65 / 2 ≤ x) :
    oddUpperLossProfile x = oddPrimeLoss x := by
  by_cases h40 : x ≤ 40
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_65div2_40 x hx h40
    by_cases hmid : x ≤ 69 / 2
    · rw [oddUpperLossProfile, hR, hS,
        oddPrimeLoss_65div2_69div2 x hx hmid,
        min_eq_right (show 48 + (105 - 2 * x) ≤ (96 : ℝ) by linarith),
        min_eq_left (show 48 + (105 - 2 * x) ≤ 2 * (105 - 2 * x) + 12 by
          linarith)]
      ring
    · rw [oddUpperLossProfile_of_second x (105 - 2 * x) 12 hR hS
        (by linarith) (by linarith),
        oddPrimeLoss_69div2_40 x (by linarith) h40]
      ring
  by_cases h52 : x ≤ 52
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_40_52 x (by linarith) h52
    rw [oddUpperLossProfile_of_second x (65 - x) (52 - x) hR hS
      (by linarith) (by linarith),
      oddPrimeLoss_40_58 x (by linarith) (by linarith)]
    ring
  by_cases h58 : x ≤ 58
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_52_58 x (by linarith) h58
    rw [oddUpperLossProfile_of_second x (117 - 2 * x) (x - 52) hR hS
      (by linarith) (by linarith),
      oddPrimeLoss_40_58 x (by linarith) h58]
    ring
  by_cases h59 : x ≤ 59
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_58_59 x (by linarith) h59
    rw [oddUpperLossProfile_of_second x (59 - x) 6 hR hS
      (by linarith) (by linarith),
      oddPrimeLoss_58_59 x (by linarith) h59]
    ring
  by_cases h65 : x ≤ 65
  · obtain ⟨hR, hS⟩ := oddUpperProfiles_59_65 x (by linarith) h65
    rw [oddUpperLossProfile_of_second x 0 (65 - x) hR hS
      (by linarith) (by linarith),
      oddPrimeLoss_59_65 x (by linarith) h65]
    ring
  obtain ⟨hR, hS⟩ := oddUpperProfiles_of_ge_65 x (by linarith)
  rw [oddUpperLossProfile_of_second x 0 0 hR hS (by norm_num) (by norm_num),
    oddPrimeLoss_of_ge_65 x (by linarith)]
  ring

end InternalCatalan

end



namespace InternalCatalan

theorem oddUpperRankCount_eq_nat (N p : ℕ) :
    oddUpperRankCount N p =
      (L N - p) + (L N - p - A N) +
        (H N - p - max (b N) (L N - p)) := by
  unfold oddUpperRankCount
  omega

theorem oddUpperSimpleCount_eq_nat (N p : ℕ) :
    oddUpperSimpleCount N p =
      (min (A N) (L N - p) - b N) +
        (min (b N) (H N - p) - (L N - p)) := by
  unfold oddUpperSimpleCount
  omega

theorem oddUpperRetainedCount_eq (N p : ℕ) (hN : 0 < N)
    (hp : p ≤ H N) (hhalf : H N ≤ 2 * p) :
    (L N - b N) - (min (A N) (L N - p) - b N) -
        (min p (L N) - max (b N) (H N - p)) =
      oddUpperRankCount N p := by
  rw [oddUpperRankCount_eq_nat]
  unfold L H A b at *
  omega

theorem oddUpperSimplePhysicalCount_eq (N p : ℕ) :
    (min (A N) (L N - p) - b N) +
        (min (b N) (H N - p) - (L N - p)) =
      oddUpperSimpleCount N p :=
  (oddUpperSimpleCount_eq_nat N p).symm





private theorem oddCount_mul_max {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    c * max u v = max (c * u) (c * v) := by
  rcases le_total u v with huv | hvu
  · rw [max_eq_right huv, max_eq_right (mul_le_mul_of_nonneg_left huv hc)]
  · rw [max_eq_left hvu, max_eq_left (mul_le_mul_of_nonneg_left hvu hc)]

private theorem oddCount_mul_min {c : ℝ} (hc : 0 ≤ c) (u v : ℝ) :
    c * min u v = min (c * u) (c * v) := by
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv, min_eq_left (mul_le_mul_of_nonneg_left huv hc)]
  · rw [min_eq_right hvu, min_eq_right (mul_le_mul_of_nonneg_left hvu hc)]

theorem oddLowerPairCountReal_mul (N : ℕ) (x : ℝ) :
    oddLowerPairCountReal N ((N : ℝ) * x) = (N : ℝ) * oddLowerPairProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddLowerPairCountReal, oddLowerPairProfile, L, A, b, H,
    Nat.cast_mul, Nat.cast_ofNat, oddCount_mul_max hN, oddCount_mul_min hN,
    mul_sub, mul_zero]
  ring_nf

theorem oddLowerCountLossReal_mul (N : ℕ) (x : ℝ) :
    oddLowerCountLossReal N ((N : ℝ) * x) = (N : ℝ) * oddLowerLossProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddLowerCountLossReal, oddLowerPairCountReal_mul, oddLowerLossProfile,
    n, q, Nat.cast_mul, Nat.cast_ofNat, oddCount_mul_max hN,
    mul_sub, mul_zero]
  ring_nf

theorem oddUpperRankCountReal_mul (N : ℕ) (x : ℝ) :
    oddUpperRankCountReal N ((N : ℝ) * x) = (N : ℝ) * oddUpperRankProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddUpperRankCountReal, oddUpperRankProfile, L, A, b, H,
    Nat.cast_mul, Nat.cast_ofNat, oddCount_mul_max hN,
    mul_add, mul_sub, mul_zero]
  ring_nf

theorem oddUpperSimpleCountReal_mul (N : ℕ) (x : ℝ) :
    oddUpperSimpleCountReal N ((N : ℝ) * x) = (N : ℝ) * oddUpperSimpleProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddUpperSimpleCountReal, oddUpperSimpleProfile, L, A, b, H,
    Nat.cast_mul, Nat.cast_ofNat, oddCount_mul_max hN, oddCount_mul_min hN,
    mul_add, mul_sub, mul_zero]
  ring_nf

theorem oddUpperCountLossReal_mul (N : ℕ) (x : ℝ) :
    oddUpperCountLossReal N ((N : ℝ) * x) = (N : ℝ) * oddUpperLossProfile x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [oddUpperCountLossReal, oddUpperRankCountReal_mul,
    oddUpperSimpleCountReal_mul, oddUpperLossProfile, n, Nat.cast_mul,
    Nat.cast_ofNat, oddCount_mul_min hN, mul_add]
  ring_nf

private theorem oddCount_scale_cancel (N : ℕ) (hN : 0 < N) (p : ℝ) :
    (N : ℝ) * (p / (N : ℝ)) = p := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hN']

theorem oddLowerPairCountReal_scaled (N : ℕ) (p : ℝ) (hN : 0 < N) :
    oddLowerPairCountReal N p = (N : ℝ) * oddLowerPairProfile (p / (N : ℝ)) := by
  have h := oddLowerPairCountReal_mul N (p / (N : ℝ))
  rw [oddCount_scale_cancel N hN p] at h
  exact h

theorem oddUpperRankCountReal_scaled (N : ℕ) (p : ℝ) (hN : 0 < N) :
    oddUpperRankCountReal N p = (N : ℝ) * oddUpperRankProfile (p / (N : ℝ)) := by
  have h := oddUpperRankCountReal_mul N (p / (N : ℝ))
  rw [oddCount_scale_cancel N hN p] at h
  exact h

theorem oddUpperSimpleCountReal_scaled (N : ℕ) (p : ℝ) (hN : 0 < N) :
    oddUpperSimpleCountReal N p = (N : ℝ) * oddUpperSimpleProfile (p / (N : ℝ)) := by
  have h := oddUpperSimpleCountReal_mul N (p / (N : ℝ))
  rw [oddCount_scale_cancel N hN p] at h
  exact h

theorem oddLowerCountLossReal_eq (N : ℕ) (p : ℝ) (hN : 0 < N)
    (hp : 2 * p ≤ (H N : ℝ)) :
    oddLowerCountLossReal N p = (N : ℝ) * oddPrimeLoss (p / (N : ℝ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : p / (N : ℝ) ≤ 65 / 2 := by
    apply (div_le_iff₀ hN').2
    simp only [H, Nat.cast_mul, Nat.cast_ofNat] at hp
    linarith
  have h := oddLowerCountLossReal_mul N (p / (N : ℝ))
  rw [oddCount_scale_cancel N hN p, oddLowerLossProfile_eq _ hx] at h
  exact h

theorem oddUpperCountLossReal_eq (N : ℕ) (p : ℝ) (hN : 0 < N)
    (hp : (H N : ℝ) ≤ 2 * p) :
    oddUpperCountLossReal N p = (N : ℝ) * oddPrimeLoss (p / (N : ℝ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 65 / 2 ≤ p / (N : ℝ) := by
    apply (le_div_iff₀ hN').2
    simp only [H, Nat.cast_mul, Nat.cast_ofNat] at hp
    linarith
  have h := oddUpperCountLossReal_mul N (p / (N : ℝ))
  rw [oddCount_scale_cancel N hN p, oddUpperLossProfile_eq _ hx] at h
  exact h





theorem oddLowerPairCount_scaled (N p : ℕ) (hN : 0 < N) :
    (oddLowerPairCount N p : ℝ) =
      (N : ℝ) * oddLowerPairProfile ((p : ℝ) / (N : ℝ)) := by
  rw [oddLowerPairCount_cast]
  exact oddLowerPairCountReal_scaled N p hN

theorem oddUpperRankCount_scaled (N p : ℕ) (hN : 0 < N) :
    (oddUpperRankCount N p : ℝ) =
      (N : ℝ) * oddUpperRankProfile ((p : ℝ) / (N : ℝ)) := by
  rw [oddUpperRankCount_cast]
  exact oddUpperRankCountReal_scaled N p hN

theorem oddUpperSimpleCount_scaled (N p : ℕ) (hN : 0 < N) :
    (oddUpperSimpleCount N p : ℝ) =
      (N : ℝ) * oddUpperSimpleProfile ((p : ℝ) / (N : ℝ)) := by
  rw [oddUpperSimpleCount_cast]
  exact oddUpperSimpleCountReal_scaled N p hN

theorem oddLowerCountLoss_eq (N p : ℕ) (hN : 0 < N) (hp : 2 * p ≤ H N) :
    (oddLowerCountLoss N p : ℝ) =
      (N : ℝ) * oddPrimeLoss ((p : ℝ) / (N : ℝ)) := by
  rw [oddLowerCountLoss_cast]
  apply oddLowerCountLossReal_eq N p hN
  exact_mod_cast hp

theorem oddUpperCountLoss_eq (N p : ℕ) (hN : 0 < N) (hp : H N ≤ 2 * p) :
    (oddUpperCountLoss N p : ℝ) =
      (N : ℝ) * oddPrimeLoss ((p : ℝ) / (N : ℝ)) := by
  rw [oddUpperCountLoss_cast]
  apply oddUpperCountLossReal_eq N p hN
  exact_mod_cast hp

def oddCountLoss (N p : ℕ) : ℕ :=
  if 2 * p ≤ H N then oddLowerCountLoss N p else oddUpperCountLoss N p

theorem oddCountLoss_eq (N p : ℕ) (hN : 0 < N) :
    (oddCountLoss N p : ℝ) =
      (N : ℝ) * oddPrimeLoss ((p : ℝ) / (N : ℝ)) := by
  by_cases hp : 2 * p ≤ H N
  · rw [oddCountLoss, ite_eq_left hp]
    exact oddLowerCountLoss_eq N p hN hp
  · rw [oddCountLoss, ite_eq_right hp]
    exact oddUpperCountLoss_eq N p hN (by omega)

end InternalCatalan



noncomputable section

namespace InternalCatalan

open Classical

def oddLowerPairSet (N p : ℕ) : Finset ℕ :=
  Finset.Ico (max (b N) (H N - 2 * p)) (min (min p (L N - p)) (A N))

def oddLowerHighSet (N p : ℕ) : Finset ℕ :=
  (oddLowerPairSet N p).image (fun ell => p + ell)

def oddLowerRetainedSet (N p : ℕ) : Finset ℕ :=
  Finset.Ico (b N) (L N) \ oddLowerHighSet N p

theorem oddLower_prime_lt_L {N p : ℕ} (hN : 0 < N) (hp : 2 * p ≤ H N) :
    p < L N := by unfold H L at *; omega

theorem oddLowerPairSet_bounds {N p ell : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) (hell : ell ∈ oddLowerPairSet N p) :
    b N ≤ ell ∧ ell < p ∧ H N ≤ ell + 2 * p ∧
      p + ell < L N ∧ ell < A N := by
  have hpL := oddLower_prime_lt_L hN hp
  dsimp [oddLowerPairSet] at hell
  simp only [Finset.mem_Ico, max_le_iff, lt_min_iff] at hell
  omega

theorem oddLowerPairSet_mem_pool {N p ell : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) (hell : ell ∈ oddLowerPairSet N p) :
    ell ∈ Finset.Ico (b N) (L N) := by
  have h := oddLowerPairSet_bounds hN hp hell
  exact Finset.mem_Ico.mpr ⟨h.1, by omega⟩

theorem oddLowerHighSet_subset_pool {N p : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) : oddLowerHighSet N p ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hj
  have h := oddLowerPairSet_bounds hN hp hell
  exact Finset.mem_Ico.mpr ⟨by omega, h.2.2.2.1⟩

theorem oddLowerPairSet_mem_retained {N p ell : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) (hell : ell ∈ oddLowerPairSet N p) :
    ell ∈ oddLowerRetainedSet N p := by
  refine Finset.mem_sdiff.mpr ⟨oddLowerPairSet_mem_pool hN hp hell, ?_⟩
  intro hhigh
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hhigh
  have h := oddLowerPairSet_bounds hN hp hell
  omega

theorem oddLowerHighSet_card (N p : ℕ) :
    (oddLowerHighSet N p).card = (oddLowerPairSet N p).card := by
  apply Finset.card_image_of_injective
  intro i j hij
  change p + i = p + j at hij
  omega

theorem oddLowerPairSet_card {N p : ℕ} (hN : 0 < N) (hp : 2 * p ≤ H N) :
    (oddLowerPairSet N p).card = oddLowerPairCount N p := by
  have hpL := oddLower_prime_lt_L hN hp
  rw [oddLowerPairSet, Nat.card_Ico]
  unfold oddLowerPairCount
  omega

theorem oddLowerRetainedSet_card {N p : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) :
    (oddLowerRetainedSet N p).card = n N + q N - oddLowerPairCount N p := by
  rw [oddLowerRetainedSet, Finset.card_sdiff_of_subset (oddLowerHighSet_subset_pool hN hp),
    oddLowerHighSet_card, oddLowerPairSet_card hN hp, Nat.card_Ico,
    L_eq_n_add_b_add_q]
  omega

theorem oddLowerPairCount_le_pool {N p : ℕ} (hN : 0 < N)
    (hp : 2 * p ≤ H N) : oddLowerPairCount N p ≤ n N + q N := by
  have h := Finset.card_le_card (oddLowerHighSet_subset_pool hN hp)
  rw [oddLowerHighSet_card, oddLowerPairSet_card hN hp, Nat.card_Ico,
    L_eq_n_add_b_add_q] at h
  omega

end InternalCatalan

end

end OAI
