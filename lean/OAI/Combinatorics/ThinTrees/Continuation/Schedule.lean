import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Interior

namespace OAI

/-! Continuation schedule. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma nthRoot_le_real_root (d r : ℕ) (hd : 0 < d) :
    (Nat.nthRoot d r:ℝ) ≤ (r:ℝ)^(1/(d:ℝ)) := by
  rw [one_div,Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_pos.mpr hd),Real.rpow_natCast]
  exact_mod_cast Nat.pow_nthRoot_le (n:=d) (a:=r) (.inl hd.ne')

lemma real_root_lt_nthRoot_add (d r : ℕ) (hd : 0 < d) :
    (r:ℝ)^(1/(d:ℝ)) < (Nat.nthRoot d r:ℝ)+1 := by
  rw [one_div,Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg _) (by positivity)
    (Nat.cast_pos.mpr hd),Real.rpow_natCast]
  exact_mod_cast Nat.lt_pow_nthRoot_add_one hd.ne' r

lemma nthRoot_pos (d r : ℕ) (hd : 0 < d) (hr : 0 < r) :
    1 ≤ Nat.nthRoot d r := by
  rw [Nat.le_nthRoot_iff hd.ne',one_pow]
  exact hr

def gain (r : ℕ) : ℚ := 1/(Nat.nthRoot 8 r:ℚ)

def blocks (r : ℕ) : ℕ := Nat.nthRoot 16 r

def blockLength (m : ℕ) : ℕ := 32*(m+1)

def scheduleLength (m r : ℕ) : ℕ := blockLength m*blocks r

lemma gain_bounds (r : ℕ) (hr : 0 < r) :
    (r:ℝ)^(-1/8:ℝ) ≤ (gain r:ℝ) ∧ (gain r:ℝ) ≤ 2*(r:ℝ)^(-1/8:ℝ) := by
  have hroot := nthRoot_le_real_root 8 r (by norm_num)
  have hr0 : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hu1 : (1:ℝ) ≤ Nat.nthRoot 8 r := by exact_mod_cast nthRoot_pos 8 r (by norm_num) hr
  have hup := real_root_lt_nthRoot_add 8 r (by norm_num)
  have hp : 0 < (r:ℝ)^(1/8:ℝ) := Real.rpow_pos_of_pos hr0 _
  have he : (r:ℝ)^(-1/8:ℝ)=1/((r:ℝ)^(1/8:ℝ)) := by
    simp only [show (-1/8:ℝ)= -(1/8:ℝ) by ring,Real.rpow_neg hr0.le,one_div]
  simp only [Nat.cast_ofNat] at hroot hup
  rw [he]
  have hg : (gain r:ℝ)=1/(Nat.nthRoot 8 r:ℝ) := by simp [gain]
  rw [hg]
  constructor
  · exact one_div_le_one_div_of_le (by linarith only [hu1]) hroot
  · have hu0 : 0 < (Nat.nthRoot 8 r:ℝ) := by linarith only [hu1]
    apply (div_le_iff₀ hu0).mpr
    rw [show 2*(1/((r:ℝ)^(1/8:ℝ)))*(Nat.nthRoot 8 r:ℝ)=
      (2*(Nat.nthRoot 8 r:ℝ))/((r:ℝ)^(1/8:ℝ)) by ring]
    apply (le_div_iff₀ hp).mpr
    linarith only [hu1,hup]

lemma blockLength_step (m : ℕ) : (blockLength m:ℝ)*continuationStep m=1 := by
  unfold blockLength continuationStep continuationBaseline
  push_cast
  field_simp

lemma blocks_le_root (r : ℕ) : (blocks r:ℝ) ≤ (r:ℝ)^(1/16:ℝ) :=
  nthRoot_le_real_root 16 r (by norm_num)

lemma schedule_loss_bound (r : ℕ) (hr : 0 < r) :
    2*(gain r:ℝ)*(blocks r:ℝ) ≤ 4*(r:ℝ)^(-1/16:ℝ) := by
  have hr0 : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hg := (gain_bounds r hr).2
  have hU := blocks_le_root r
  have hh := mul_le_mul hg hU (Nat.cast_nonneg _) (by positivity : 0 ≤ 2*(r:ℝ)^(-1/8:ℝ))
  have he : (r:ℝ)^(-1/8:ℝ)*(r:ℝ)^(1/16:ℝ)=(r:ℝ)^(-1/16:ℝ) := by
    rw [←Real.rpow_add hr0]
    congr 1
    norm_num
  rw [mul_assoc,he] at hh
  linarith only [hh]

lemma large_blocks (r : ℕ) (hr : 64^16 ≤ r) : 64 ≤ blocks r := by
  exact (Nat.le_nthRoot_iff (by norm_num : 16≠0)).mpr hr

lemma large_gain (r : ℕ) (hr : 64^16 ≤ r) : 3 ≤ (gain r:ℝ)*r := by
  have hu2 : 2 ≤ Nat.nthRoot 8 r := (Nat.le_nthRoot_iff (by norm_num : 8≠0)).mpr
    (le_trans (by norm_num : 2^8 ≤ 64^16) hr)
  have hpow : 3*Nat.nthRoot 8 r ≤ (Nat.nthRoot 8 r)^8 := by
    have hh : 3 ≤ (Nat.nthRoot 8 r)^7 := (by norm_num : 3 ≤ 2^7).trans (Nat.pow_le_pow_left hu2 7)
    calc
      _ ≤ (Nat.nthRoot 8 r)^7*Nat.nthRoot 8 r := Nat.mul_le_mul_right _ hh
      _ = _ := (pow_succ _ _).symm
  have hh := hpow.trans (Nat.pow_nthRoot_le (n:=8) (a:=r) (by left; norm_num))
  have hreal : (3:ℝ)*Nat.nthRoot 8 r ≤ r := by exact_mod_cast hh
  have hp : 0 < (Nat.nthRoot 8 r:ℝ) := by exact_mod_cast (show 0 < Nat.nthRoot 8 r by omega)
  simp only [gain,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  rw [one_div,inv_mul_eq_div,le_div_iff₀ hp]
  exact hreal

lemma large_schedule_loss (r : ℕ) (hr : 64^16 ≤ r) :
    2*(gain r:ℝ)*(blocks r:ℝ) ≤ 1/4 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num : 0 < 64^16) hr
  have hU : (64:ℝ) ≤ (blocks r:ℝ) := by exact_mod_cast large_blocks r hr
  have hp := hU.trans (blocks_le_root r)
  have hi : (r:ℝ)^(-1/16:ℝ) ≤ 1/64 := by
    rw [show (-1/16:ℝ)= -(1/16:ℝ) by ring,Real.rpow_neg (Nat.cast_nonneg _),←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp
  linarith only [schedule_loss_bound r hr0,hi]

lemma block_growth (m : ℕ) : 2 ≤ (1+continuationStep m)^(blockLength m) := by
  have ht := (continuation_parameters m).2.2.2.1
  have hh := one_add_mul_le_pow (by linarith : -2 ≤ continuationStep m) (blockLength m)
  rw [blockLength_step] at hh
  norm_num only [one_add_one_eq_two] at hh
  exact hh

lemma fourth_power_le_two_pow (U : ℕ) (hU : 64 ≤ U) : 2*(U+1)^4 ≤ 2^U := by
  induction U,hU using Nat.le_induction with
  | base => norm_num
  | succ U hU ih =>
    have hstep : (U+2)^4 ≤ 2*(U+1)^4 := by

      have hh : 16*(U+2) ≤ 17*(U+1) := by omega
      have hpow := Nat.pow_le_pow_left hh 4
      rw [mul_pow,mul_pow] at hpow
      norm_num only [Nat.reducePow] at hpow
      omega
    rw [pow_succ 2 U]
    have he : U+1+1=U+2 := by omega
    rw [he]
    omega

lemma schedule_growth (m r : ℕ) (hr : 64^16 ≤ r) :
    (r:ℝ)^(1/4:ℝ) ≤ (1+continuationStep m)^(scheduleLength m r)/2 := by
  have hU := large_blocks r hr
  have hpow := fourth_power_le_two_pow (blocks r) hU
  have hg := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (block_growth m) (blocks r)
  rw [←pow_mul,←scheduleLength] at hg
  have hroot : (r:ℝ)^(1/4:ℝ) ≤ ((blocks r:ℝ)+1)^4 := by
    have hh := Nat.lt_pow_nthRoot_add_one (by norm_num : 16≠0) r
    have hc : (r:ℝ) ≤ ((blocks r:ℝ)+1)^16 := by exact_mod_cast hh.le
    rw [one_div,Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) (by positivity) (by norm_num : (0:ℝ)<4)]
    simpa only [Real.rpow_ofNat,←pow_mul,Nat.reduceMul] using hc
  have hc : 2*((blocks r:ℝ)+1)^4 ≤ (2:ℝ)^(blocks r) := by exact_mod_cast hpow
  linarith only [hg,hroot,hc]

lemma schedule_length_bound (m r : ℕ) (hr : r ≤ m) : scheduleLength m r ≤ 32*(m+1)^2 := by
  have hu : blocks r ≤ r := by
    have hh := Nat.pow_nthRoot_le (n:=16) (a:=r) (by left; norm_num)
    exact (Nat.le_self_pow (by norm_num : 16≠0) _).trans hh
  unfold scheduleLength blockLength
  nlinarith only [hu,hr]

lemma scheduleLength_step (m r : ℕ) : (scheduleLength m r:ℝ)*continuationStep m=blocks r := by
  simp only [scheduleLength,Nat.cast_mul]
  calc
    _ = (blocks r:ℝ)*((blockLength m:ℝ)*continuationStep m) := by ring
    _ = _ := by rw [blockLength_step,mul_one]

lemma cost_le_schedule (m r i : ℕ) (hi : i ≤ scheduleLength m r) :
    (i:ℝ)*(2*(gain r:ℝ)*r*continuationStep m) ≤ 2*(gain r:ℝ)*(blocks r:ℝ)*r := by
  have hg : 0 ≤ (gain r:ℝ) := by simp only [gain,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]; positivity
  have hh := mul_le_mul_of_nonneg_right (show (i:ℝ) ≤ scheduleLength m r by exact_mod_cast hi)
    (continuation_parameters m).2.2.2.1
  rw [scheduleLength_step] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*(gain r:ℝ)*r)
  nlinarith only [hmul]

lemma running_quality_lower (m r i : ℕ) (hr : 64^16 ≤ r) (hi : i ≤ scheduleLength m r) :
    3*(r:ℝ)/4 ≤ (r:ℝ)-(i:ℝ)*(2*(gain r:ℝ)*r*continuationStep m) := by
  have hh := cost_le_schedule m r i hi
  have hl := mul_le_mul_of_nonneg_right (large_schedule_loss r hr) (Nat.cast_nonneg (α:=ℝ) r)
  linarith only [hh,hl]

lemma running_quality_loss (m r i : ℕ) (hr : 0 < r) (hi : i ≤ scheduleLength m r) :
    (1-4*(r:ℝ)^(-1/16:ℝ))*r ≤ (r:ℝ)-(i:ℝ)*(2*(gain r:ℝ)*r*continuationStep m) := by
  have hh := cost_le_schedule m r i hi
  have hl := mul_le_mul_of_nonneg_right (schedule_loss_bound r hr) (Nat.cast_nonneg (α:=ℝ) r)
  nlinarith only [hh,hl]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
