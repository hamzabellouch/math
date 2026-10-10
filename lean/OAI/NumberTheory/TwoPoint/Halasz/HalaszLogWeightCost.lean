import OAI.NumberTheory.TwoPoint.Halasz.HalaszScaleRatios

namespace OAI

/-! A single explicit coefficient cost for every active Taylor degree. -/
namespace TwoPointCorrelations

noncomputable def halaszLogWeightCost (k r : ℕ) : ℝ :=
  (8:ℝ)^(k+2)*(r+k+1)

lemma halasz_log_weight_cost_pos (k r : ℕ) : 0<halaszLogWeightCost k r := by
  unfold halaszLogWeightCost
  positivity

lemma halasz_log_degree_cost {k r : ℕ} (hr : 1≤r) (j : Fin k) :
    (5/2:ℝ)*(2:ℝ)^(j.val+1)+(r:ℝ)/(Real.pi*(j.val+1))+
      Real.pi*(j.val+1)/(r:ℝ)*(8:ℝ)^(j.val+1) ≤ halaszLogWeightCost k r := by
  have hrR : 1≤(r:ℝ) := by exact_mod_cast hr
  have hd : 1≤(j.val:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j.val)
  have hdk : (j.val:ℝ)+1≤k := by exact_mod_cast (show j.val+1≤k by omega)
  have hpi : 1≤Real.pi*((j.val:ℝ)+1) := by nlinarith [Real.pi_gt_three]
  have hdiv : (r:ℝ)/(Real.pi*(j.val+1))≤r := div_le_self (by positivity) hpi
  have hdiv' : Real.pi*(j.val+1)/(r:ℝ)≤4*k := by
    apply (div_le_iff₀ (by positivity : 0<(r:ℝ))).mpr
    nlinarith [Real.pi_lt_four,show (0:ℝ)≤k by positivity]
  have hdN : j.val+1≤k := by omega
  have hpow8 : (8:ℝ)^(j.val+1)≤(8:ℝ)^k := pow_le_pow_right₀ (by norm_num) hdN
  have hpow2 : (2:ℝ)^(j.val+1)≤(8:ℝ)^k :=
    (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by norm_num : (2:ℝ)≤8) _).trans hpow8
  have hterm := mul_le_mul hdiv' hpow8 (by positivity) (by positivity : (0:ℝ)≤4*k)
  have hP : 1≤(8:ℝ)^k := one_le_pow₀ (by norm_num)
  have hrP : (r:ℝ)≤r*(8:ℝ)^k := le_mul_of_one_le_right (by positivity) hP
  unfold halaszLogWeightCost
  rw [show (8:ℝ)^(k+2)=64*(8:ℝ)^k by rw [pow_add]; norm_num only [pow_two]; ring]
  have hkP : 0≤(k:ℝ)*(8:ℝ)^k := by positivity
  have hrP0 : 0≤(r:ℝ)*(8:ℝ)^k := by positivity
  nlinarith only [hpow2,hdiv,hterm,hP,hrP,hkP,hrP0]

lemma halasz_log_coordinate_saving {k r M : ℕ} (hr : 1≤r) (hM : 1≤M)
    {t z N α lam η : ℝ} (hN : 1≤N) (hz : N≤z) (hzhi : z≤2*N)
    (ht : |t|=N^lam) (hscale : N^α≤2*(M:ℝ)) (j : Fin k)
    (h₁ : η≤α*(j.val+1)) (h₂ : η≤(j.val+1)-lam)
    (h₃ : η≤lam-(j.val+1)+2*α*(j.val+1)) :
    halaszNormalizedWeight r M (halaszLogCoefficient t z) j ≤
      halaszLogWeightCost k r*N^(-η) := by
  have hN0 : 0<N := by linarith
  have hz0 : 0<z := hN0.trans_le hz
  have ht0 : t≠0 := by
    intro ht0
    have hp := Real.rpow_pos_of_pos hN0 lam
    rw [ht0,abs_zero] at ht
    linarith
  have hrate := halasz_three_degree_rates (d := ((j.val+1:ℕ):ℝ)) hN
    (by simpa only [Nat.cast_add,Nat.cast_one] using h₁)
    (by simpa only [Nat.cast_add,Nat.cast_one] using h₂)
    (by simpa only [Nat.cast_add,Nat.cast_one] using h₃)
  have ha := (halasz_inverse_short_power hM hN0 hscale (j.val+1)).trans
    (mul_le_mul_of_nonneg_left hrate.1 (by positivity : (0:ℝ)≤2^(j.val+1)))
  have hb := (halasz_height_over_long_power hN0 hz ht (j.val+1)).trans hrate.2.1
  have he := (halasz_long_over_short_height hM hN0 hz0.le hzhi ht hscale (j.val+1)).trans
    (mul_le_mul_of_nonneg_left hrate.2.2 (by positivity : (0:ℝ)≤8^(j.val+1)))
  have hh := halasz_log_weight_bound (B := 1) hr hM ht0 hz0 j ha
    (by simpa only [one_mul] using hb) he
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using halasz_log_degree_cost hr j)
    (Real.rpow_nonneg hN0.le _)

end TwoPointCorrelations

end OAI
