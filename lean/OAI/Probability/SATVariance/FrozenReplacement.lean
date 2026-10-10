import OAI.Probability.SATVariance.FirstFailure

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def killRatio (u b s : ℕ) : ℝ := (b.choose s : ℝ) / (2 ^ s * u.choose s)

lemma killRatio_nonneg (u b s : ℕ) : 0 ≤ killRatio u b s := by
  unfold killRatio
  positivity

lemma killRatio_zero (u b : ℕ) : killRatio u b 0 = 1 := by
  simp [killRatio]

lemma killRatio_eq_zero {u b s : ℕ} (hbs : b < s) : killRatio u b s = 0 := by
  simp [killRatio, Nat.choose_eq_zero_of_lt hbs]

lemma killRatio_succ {u b s : ℕ} (hsu : s < u) (hsb : s ≤ b) :
    killRatio u b (s + 1) = killRatio u b s * ((b : ℝ) - s) / (2 * (u - s)) := by
  have hu : (0 : ℝ) < u.choose s := by exact_mod_cast Nat.choose_pos hsu.le
  have hu' : (0 : ℝ) < u.choose (s+1) := by exact_mod_cast Nat.choose_pos hsu
  have hus : (0 : ℝ) < (u : ℝ) - s := sub_pos.mpr (by exact_mod_cast hsu)
  have hb := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq b s)
  have hn := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq u s)
  push_cast [Nat.cast_sub hsb] at hb
  push_cast [Nat.cast_sub hsu.le] at hn
  unfold killRatio
  rw [pow_succ]
  apply (div_eq_iff (by positivity : (2 : ℝ)^s * 2 * u.choose (s+1) ≠ 0)).2
  field_simp
  nlinarith [mul_pos hu hus]

lemma killRatio_le_density_pow {u b s : ℕ} (hbu : b ≤ u) (hsu : s ≤ u) :
    killRatio u b s ≤ ((b : ℝ) / (2 * u)) ^ s := by
  induction s with
  | zero => simp [killRatio_zero]
  | succ s ih =>
    by_cases hbs : b < s+1
    · rw [killRatio_eq_zero hbs]
      positivity
    · have hsb : s ≤ b := by omega
      have hsu' : s < u := by omega
      have hus : (0 : ℝ) < (u : ℝ) - s := sub_pos.mpr (by exact_mod_cast hsu')
      have hu : (0 : ℝ) < u := by exact_mod_cast (Nat.zero_le s).trans_lt hsu'
      have hbu' : (b : ℝ) ≤ u := by exact_mod_cast hbu
      have hs : (0 : ℝ) ≤ s := by positivity
      have hfactor : ((b : ℝ)-s) / (2 * (u-s)) ≤ (b : ℝ)/(2*u) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      rw [killRatio_succ hsu' hsb, mul_div_assoc, pow_succ]
      have hbs₀ : (0 : ℝ) ≤ (b : ℝ) - s := sub_nonneg.mpr (by exact_mod_cast hsb)
      exact mul_le_mul (ih (by omega)) hfactor (by positivity) (by positivity)

lemma killRatio_le_half_pow {u b s : ℕ} (hu : 0 < u) (hbu : b ≤ u) (hsu : s ≤ u) :
    killRatio u b s ≤ ((1 : ℝ)/2)^s := by
  apply (killRatio_le_density_pow hbu hsu).trans
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*u)).2
  have hb : (b : ℝ) ≤ u := by exact_mod_cast hbu
  nlinarith

lemma killRatio_pos {u b s : ℕ} (hsb : s ≤ b) (hsu : s ≤ u) :
    0 < killRatio u b s := by
  unfold killRatio
  have hb : (0 : ℝ) < b.choose s := by exact_mod_cast Nat.choose_pos hsb
  have hu : (0 : ℝ) < u.choose s := by exact_mod_cast Nat.choose_pos hsu
  positivity

lemma killRatio_root_le {u b r : ℕ} (hr : 0 < r) (hbu : b ≤ u) (hru : r ≤ u) :
    (killRatio u b r) ^ ((r : ℝ)⁻¹) ≤ (b : ℝ) / (2*u) := by
  have hr₀ : (r : ℝ) ≠ 0 := by positivity
  have h := Real.rpow_le_rpow (killRatio_nonneg u b r)
    (killRatio_le_density_pow hbu hru) (by positivity : (0 : ℝ) ≤ (r : ℝ)⁻¹)
  rw [← Real.rpow_natCast_mul (by positivity), mul_inv_cancel₀ hr₀,
    Real.rpow_one] at h
  exact h

lemma frozen_power {u b r : ℕ} (hr : 1 ≤ r) (hbu : b ≤ u) (hrb : r+1 ≤ b) :
    (killRatio u b r) ^ (((r : ℝ)+1)/r) / (r+1) ≤ killRatio u b (r+1) := by
  have hru : r < u := by omega
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast hr
  have hu₀ : (0 : ℝ) < u := by exact_mod_cast (Nat.zero_le r).trans_lt hru
  have hus : (0 : ℝ) < (u : ℝ)-r := sub_pos.mpr (by exact_mod_cast hru)
  have hrb' : (r : ℝ)+1 ≤ b := by exact_mod_cast hrb
  have hbu' : (b : ℝ) ≤ u := by exact_mod_cast hbu
  have hstep : (b : ℝ)/(2*u)/(r+1) ≤ ((b : ℝ)-r)/(2*(u-r)) := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hrb') (le_of_lt hr₀)]
  have he : ((r : ℝ)+1)/r = 1+(r : ℝ)⁻¹ := by field_simp
  rw [he, Real.rpow_add_of_nonneg (killRatio_nonneg u b r) zero_le_one (by positivity),
    Real.rpow_one, mul_div_assoc, killRatio_succ hru (by omega), mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (killRatio_nonneg u b r)
  exact (div_le_div_of_nonneg_right (killRatio_root_le (by omega) hbu hru.le)
    (by positivity)).trans hstep

end RandomKSAT

end

end OAI
