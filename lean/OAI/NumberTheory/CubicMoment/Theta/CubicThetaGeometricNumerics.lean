import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselSlopeNumerics

namespace OAI

/-! Elementary exponential and polynomial bounds for the two coordinate tails. -/
noncomputable section
namespace CubicFirstMoment

lemma cubic_exp_one_lower : (2718/1000:ℝ)≤Real.exp 1 := by
  linarith [Real.exp_one_gt_d9]

lemma cubic_exp_tail_lower : (120:ℝ)≤Real.exp (241/50:ℝ) := by
  have h4 : (2718/1000:ℝ)^4≤Real.exp 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) cubic_exp_one_lower 4
    simpa only [←Real.exp_nat_mul,Nat.cast_ofNat,mul_one] using h
  have hf := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤41/50) 4
  norm_num [Finset.sum_range_succ] at hf
  have hmul := mul_le_mul h4 hf (by norm_num) (Real.exp_pos 4).le
  rw [←Real.exp_add] at hmul
  norm_num at hmul
  linarith

lemma cubic_exp_six_lower : (400:ℝ)≤Real.exp 6 := by
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) cubic_exp_one_lower 6
  rw [←Real.exp_nat_mul] at h
  norm_num at h
  linarith

lemma cubic_nat_le_two_pow_pred {k : ℕ} (hk : 1≤k) : k≤2^(k-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  induction n with
  | zero => norm_num
  | succ n ih =>
    norm_num only [Nat.succ_sub_one] at ih ⊢
    calc
      n+1+1≤2*(n+1) := by omega
      _ ≤2*2^n := Nat.mul_le_mul_left 2 (ih (by omega))
      _ =2^(n+1) := by rw [pow_succ]; omega

lemma cubic_nat_fourth_geometric {k : ℕ} (hk : 1≤k) :
    (k:ℝ)^4≤(16:ℝ)^k/16 := by
  have h := pow_le_pow_left₀ (by positivity : (0:ℝ)≤k)
    (show (k:ℝ)≤2^(k-1) by exact_mod_cast cubic_nat_le_two_pow_pred hk) 4
  have hp : ((2:ℝ)^(k-1))^4=16^(k-1) := by
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rw [hp] at h
  have he : (16:ℝ)^k/16=16^(k-1) := by
    nth_rw 1 [←Nat.sub_add_cancel hk]
    rw [pow_add]
    norm_num
  rwa [he]

lemma cubic_exp_nat_tail_bound (k : ℕ) :
    Real.exp (-(241/50:ℝ)*(k:ℝ))≤(1/120:ℝ)^k := by
  have h : Real.exp (-(241/50:ℝ))≤1/120 := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; exact cubic_exp_tail_lower)
  calc
    _ = Real.exp (-(241/50:ℝ))^k := by rw [←Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le h k

lemma cubic_exp_nat_high_bound (k : ℕ) :
    Real.exp (-(6:ℝ)*(k:ℝ))≤(1/400:ℝ)^k := by
  have h : Real.exp (-(6:ℝ))≤1/400 := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; exact cubic_exp_six_lower)
  calc
    _ = Real.exp (-(6:ℝ))^k := by rw [←Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le h k

end CubicFirstMoment

end

end OAI
