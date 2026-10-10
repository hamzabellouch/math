import OAI.NumberTheory.CubicMoment.Estimates.TypeIShortConvolution

namespace OAI

/-! The two Mellin-height ranges used after the Type-I estimate, with
explicit power gaps and logarithmic decay of the pole term. -/
noncomputable section
namespace CubicFirstMoment

lemma typeI_bulk_power {X R T a b ε : ℝ} (hX : 0 < X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^a) (hTb : T ≤ X^b) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(1/2+ε+3*a/4+b/2) := by
  have hr := Real.rpow_le_rpow hR hRa (by norm_num : (0:ℝ) ≤ 3/4)
  rw [← Real.rpow_mul hX.le] at hr
  have ht : Real.sqrt T ≤ X^(b/2) := by
    have hh := Real.rpow_le_rpow hT hTb (by norm_num : (0:ℝ) ≤ 1/2)
    rw [← Real.rpow_mul hX.le] at hh
    calc
      Real.sqrt T = T^(1/2:ℝ) := Real.sqrt_eq_rpow _
      _ ≤ X^(b*(1/2:ℝ)) := hh
      _ = _ := by congr 1; ring
  calc
    _ ≤ X^(1/2+ε)*X^(a*(3/4:ℝ))*X^(b/2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hX.le _)) ht
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hX,← Real.rpow_add hX]; congr 1; ring

lemma typeI_first_bulk_exponent {X R T ε : ℝ} (hX : 0 < X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^(2/5:ℝ)) (hTb : T ≤ X^(1/100:ℝ)) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(161/200+ε) := by
  convert typeI_bulk_power hX hR hT hRa hTb (ε := ε) using 1; congr 1; ring

lemma typeI_second_bulk_exponent {X R T ε κ ρ : ℝ}
    (hX : 0 < X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^(1/3-κ/2)) (hTb : T ≤ X^(1/6+ρ)) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(5/6-3*κ/8+ρ/2+ε) := by
  convert typeI_bulk_power hX hR hT hRa hTb (ε := ε) using 1; congr 1; ring

lemma typeI_first_fixed_gap {X R T ε : ℝ} (hX : 1 ≤ X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^(2/5:ℝ)) (hTb : T ≤ X^(1/100:ℝ)) (hε : ε ≤ 1/100) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(5/6-1/100:ℝ) := by
  apply (typeI_first_bulk_exponent (zero_lt_one.trans_le hX) hR hT hRa hTb).trans
  exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)

lemma typeI_second_fixed_gap {X R T ε κ ρ : ℝ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRa : R ≤ X^(1/3-κ/2)) (hTb : T ≤ X^(1/6+ρ))
    (hρ : ρ ≤ κ/4) (hε : ε ≤ κ/16) :
    X^(1/2+ε)*R^(3/4:ℝ)*Real.sqrt T ≤ X^(5/6-3*κ/16) := by
  apply (typeI_second_bulk_exponent (zero_lt_one.trans_le hX) hR hT hRa hTb).trans
  exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)

lemma typeI_pole_log_saving {X T : ℝ} (hX : 0 ≤ X) (hlog : 1 ≤ Real.log X)
    (hT : Real.log X ≤ T) {B D M : ℕ} (hD : B+M ≤ D) :
    X^(5/6:ℝ)*(Real.log X)^B/T^D ≤ X^(5/6:ℝ)/(Real.log X)^M := by
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hTp : 0 < T := hLp.trans_le hT
  have hp : (Real.log X)^B/T^D ≤ 1/(Real.log X)^M := by
    apply (div_le_div_iff₀ (pow_pos hTp D) (pow_pos hLp M)).mpr
    rw [one_mul,← pow_add]
    exact (pow_le_pow_right₀ hlog hD).trans (pow_le_pow_left₀ hLp.le hT D)
  calc
    _ = X^(5/6:ℝ)*((Real.log X)^B/T^D) := by ring
    _ ≤ X^(5/6:ℝ)*(1/(Real.log X)^M) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hX _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
