import OAI.Dynamics.ConditionalShuffle.HybridCycles

namespace OAI

noncomputable section
open scoped Classical
open Filter Topology
namespace Thorp.Conditional.OverlayEnergy

def prepError (g : ℕ) : ℝ := (2^g : ℝ) * Real.sqrt
  ((Fintype.card (Position (g+3)) : ℝ) *
    ((1/2 : ℝ)^(8*(g+3)) + 32*(9/10 : ℝ)^(2^g)))

lemma prepError_nonneg (g : ℕ) : 0 ≤ prepError g := by unfold prepError; positivity

lemma error_scaled_sq (g : ℕ) : ((2^g : ℝ) * prepError g)^2 =
    (8 / 2^24 : ℝ) * (1/8 : ℝ)^g + 256 * (2^g : ℝ)^5 * (9/10 : ℝ)^(2^g) := by
  unfold prepError
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hN : (Fintype.card (Position (g+3)) : ℝ) = 8 * (2^g : ℝ) := by
    rw [card_position]; push_cast; rw [pow_add]; norm_num; ring
  rw [hN]
  have hp : (1/2 : ℝ)^(8*(g+3)) = (1/2 : ℝ)^(8*g) * (1/2 : ℝ)^24 := by
    rw [show 8*(g+3) = 8*g+24 by omega, pow_add]
  have he : (2^g : ℝ)^5 * (1/2 : ℝ)^(8*g) = (1/8 : ℝ)^g := by
    rw [← pow_mul, Nat.mul_comm g 5, pow_mul, pow_mul, ← mul_pow]
    norm_num
  rw [hp]
  calc
    _ = 8 * ((2^g : ℝ)^5 * (1/2 : ℝ)^(8*g)) * (1/2 : ℝ)^24 +
        256 * (2^g : ℝ)^5 * (9/10 : ℝ)^(2^g) := by ring
    _ = _ := by rw [he]; norm_num; ring

lemma error_scaled_tendsto : Tendsto (fun g : ℕ => (2^g : ℝ) * prepError g) atTop (nhds 0) := by
  have h₁ := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/8)
    (by norm_num : (1/8 : ℝ) < 1)).const_mul (8/2^24 : ℝ)
  have h₂ := ((tendsto_pow_const_mul_const_pow_of_lt_one 5
    (by norm_num : (0 : ℝ) ≤ 9/10) (by norm_num : (9/10 : ℝ) < 1)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))).const_mul (256 : ℝ)
  have hh := (h₁.add h₂).sqrt
  have he (g : ℕ) : Real.sqrt ((8/2^24 : ℝ)*(1/8 : ℝ)^g +
      256*(2^g : ℝ)^5*(9/10 : ℝ)^(2^g)) = (2^g : ℝ)*prepError g := by
    rw [← error_scaled_sq, Real.sqrt_sq (mul_nonneg (by positivity) (prepError_nonneg g))]
  simpa only [Function.comp_def, Nat.cast_pow, Nat.cast_ofNat, mul_zero,
    add_zero, Real.sqrt_zero, ← mul_assoc, he] using hh

lemma prepError_tendsto : Tendsto prepError atTop (nhds 0) := by
  apply squeeze_zero prepError_nonneg (fun g => ?_) error_scaled_tendsto
  exact le_mul_of_one_le_left (prepError_nonneg g) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

lemma pow_add_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a+b)^n ≤ (2 : ℝ)^n * (a^n+b^n) := by
  rcases le_total a b with hab | hba
  · calc
      _ ≤ (2*b)^n := pow_le_pow_left₀ (add_nonneg ha hb) (by linarith) n
      _ = (2 : ℝ)^n*b^n := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg ha _)) (by positivity)
  · calc
      _ ≤ (2*a)^n := pow_le_pow_left₀ (add_nonneg ha hb) (by linarith) n
      _ = (2 : ℝ)^n*a^n := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg hb _)) (by positivity)

lemma gamma_power : 2*(255/256 : ℝ)^200 < 1 := by norm_num

lemma coefficient_scaled_tendsto :
    Tendsto (fun g : ℕ => (2^g : ℝ) * coefficient g ^ 200) atTop (nhds 0) := by
  have ha : Tendsto (fun g : ℕ => (2^g : ℝ) * ((255/256 : ℝ)^(g+3))^200) atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : (0 : ℝ) ≤ 2*(255/256 : ℝ)^200) gamma_power).mul_const ((255/256 : ℝ)^600)
    convert hh using 1
    · funext g
      rw [← pow_mul, Nat.add_mul, pow_add, Nat.mul_comm g 200, pow_mul, mul_pow]
      generalize (255/256 : ℝ)^600 = C
      ring
    · simp only [zero_mul]
  have hb : Tendsto (fun g : ℕ => (2^g : ℝ) * prepError g ^ 200) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun g => by positivity)) ?_ error_scaled_tendsto
    filter_upwards [(tendsto_order.1 prepError_tendsto).2 1 (by norm_num)] with g hg
    exact mul_le_mul_of_nonneg_left
      (by simpa only [pow_one] using pow_le_pow_of_le_one (prepError_nonneg g) (le_of_lt hg) (by norm_num : 1 ≤ 200)) (by positivity)
  have hh := (ha.add hb).const_mul ((2 : ℝ)^200)
  have hc : Tendsto (fun g : ℕ => (2 : ℝ)^200 *
      ((2^g : ℝ)*((255/256 : ℝ)^(g+3))^200 + (2^g : ℝ)*prepError g^200)) atTop (nhds 0) := by
    simpa only [add_zero, mul_zero] using hh
  apply squeeze_zero (fun g => by positivity) (fun g => ?_) hc
  have hh := mul_le_mul_of_nonneg_left (pow_add_bound ((255/256 : ℝ)^(g+3))
    (prepError g) (by positivity) (prepError_nonneg g) 200) (by positivity : (0 : ℝ) ≤ 2^g)
  change (2^g : ℝ) * (((255/256 : ℝ)^(g+3)) + prepError g)^200 ≤ _
  exact hh.trans_eq (by ring)

lemma total_energy_tendsto :
    Tendsto (fun g : ℕ => (2^g : ℝ)^3 * coefficient g^800) atTop (nhds 0) := by
  have hh := coefficient_scaled_tendsto.pow 4
  simp only [zero_pow (by norm_num : 4 ≠ 0)] at hh
  apply squeeze_zero (fun g => by positivity) (fun g => ?_) hh
  rw [mul_pow, ← pow_mul (coefficient g), show 200*4=800 by omega]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (coefficient_nonneg g) _)
  exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num : 3 ≤ 4)

def marginalRate (g : ℕ) : ℝ := Real.sqrt (8 * (2^g : ℝ)^3 * coefficient g^800)

lemma marginalRate_tendsto : Tendsto marginalRate atTop (nhds 0) := by
  change Tendsto (fun g : ℕ => Real.sqrt (8 * (2^g : ℝ)^3 * coefficient g^800)) atTop (nhds 0)
  simpa only [mul_assoc, mul_zero, Real.sqrt_zero] using
    (total_energy_tendsto.const_mul 8).sqrt

end Thorp.Conditional.OverlayEnergy

end

end OAI
