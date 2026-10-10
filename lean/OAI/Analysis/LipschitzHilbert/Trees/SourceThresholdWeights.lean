import OAI.Analysis.LipschitzHilbert.Trees.SourceDensitySpatialCost

namespace OAI

/-! The numerical density-size weight has summable decay on both sides
of the unit scale, with the quarter-power density gain. -/
noncomputable section
namespace LipschitzHilbert

def ordinaryThresholdWeight (gamma eta : ℝ) : ℝ :=
  min gamma (2*eta) * Real.sqrt eta * (1+eta^(-(1/20:ℝ))) / eta

theorem min_le_quarter_interpolation {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    min a b ≤ a^(1/4:ℝ)*b^(3/4:ℝ) := by
  have haeq : a=a^(1/4:ℝ)*a^(3/4:ℝ) := by
    rw [←Real.rpow_add ha]
    norm_num
  have hbeq : b=b^(1/4:ℝ)*b^(3/4:ℝ) := by
    rw [←Real.rpow_add hb]
    norm_num
  rcases le_total a b with hab | hba
  · have hp : a^(3/4:ℝ)≤b^(3/4:ℝ) := Real.rpow_le_rpow ha.le hab (by norm_num)
    calc
      min a b = a := min_eq_left hab
      _ = a^(1/4:ℝ)*a^(3/4:ℝ) := haeq
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ha.le _)
  · have hp : b^(1/4:ℝ)≤a^(1/4:ℝ) := Real.rpow_le_rpow hb.le hba (by norm_num)
    calc
      min a b = b := min_eq_right hba
      _ = b^(1/4:ℝ)*b^(3/4:ℝ) := hbeq
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hb.le _)

theorem ordinaryThresholdWeight_nonneg {gamma eta : ℝ} (hgamma : 0≤gamma) (heta : 0≤eta) :
    0≤ordinaryThresholdWeight gamma eta := by
  dsimp [ordinaryThresholdWeight]
  positivity

theorem ordinaryThresholdWeight_small {gamma eta : ℝ} (hgamma : 0<gamma)
    (heta : 0<eta) (hsmall : eta≤1) :
    ordinaryThresholdWeight gamma eta ≤ 4*gamma^(1/4:ℝ)*eta^(1/5:ℝ) := by
  have hm : min gamma (2*eta)≤2*min gamma eta := by
    rcases le_total gamma eta with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]
      exact min_le_right _ _
  have hinterp := hm.trans (mul_le_mul_of_nonneg_left
    (min_le_quarter_interpolation hgamma heta) (by norm_num : (0:ℝ)≤2))
  have hpos : 0≤Real.sqrt eta*(1+eta^(-(1/20:ℝ)))/eta := by positivity
  have hpower : (eta^(3/4:ℝ)*Real.sqrt eta*(1+eta^(-(1/20:ℝ)))/eta)=
      eta^(1/4:ℝ)+eta^(1/5:ℝ) := by
    rw [Real.sqrt_eq_rpow,div_eq_mul_inv,←Real.rpow_neg_one]
    rw [mul_add,add_mul]
    simp only [mul_one]
    rw [←Real.rpow_add heta,←Real.rpow_add heta,←Real.rpow_add heta,←Real.rpow_add heta]
    norm_num
  calc
    _ ≤ (2*(gamma^(1/4:ℝ)*eta^(3/4:ℝ)))*
        (Real.sqrt eta*(1+eta^(-(1/20:ℝ)))/eta) := by
      simpa only [ordinaryThresholdWeight,mul_div_assoc,mul_assoc] using
        mul_le_mul_of_nonneg_right hinterp hpos
    _ = 2*gamma^(1/4:ℝ)*(eta^(1/4:ℝ)+eta^(1/5:ℝ)) := by rw [←hpower]; ring
    _ ≤ _ := by
      have hp := Real.rpow_le_rpow_of_exponent_ge heta hsmall (by norm_num : (1/5:ℝ)≤1/4)
      have hg := Real.rpow_nonneg hgamma.le (1/4:ℝ)
      nlinarith

theorem ordinaryThresholdWeight_large {gamma eta : ℝ} (hgamma : 0<gamma)
    (hgammaOne : gamma≤1) (heta : 1≤eta) :
    ordinaryThresholdWeight gamma eta ≤ 2*gamma^(1/4:ℝ)*eta^(-(1/5:ℝ)) := by
  have hetaPos : 0<eta := zero_lt_one.trans_le heta
  have hg : gamma≤gamma^(1/4:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hgamma hgammaOne (by norm_num : (1/4:ℝ)≤1)
  have hm : min gamma (2*eta)≤gamma^(1/4:ℝ) := (min_le_left _ _).trans hg
  have hpos : 0≤Real.sqrt eta*(1+eta^(-(1/20:ℝ)))/eta := by positivity
  have hpower : Real.sqrt eta*(1+eta^(-(1/20:ℝ)))/eta=
      eta^(-(1/2:ℝ))+eta^(-(11/20:ℝ)) := by
    rw [Real.sqrt_eq_rpow,div_eq_mul_inv,←Real.rpow_neg_one]
    rw [mul_add,add_mul]
    simp only [mul_one]
    rw [←Real.rpow_add hetaPos,←Real.rpow_add hetaPos,←Real.rpow_add hetaPos]
    norm_num
  calc
    _ ≤ gamma^(1/4:ℝ)*(Real.sqrt eta*(1+eta^(-(1/20:ℝ)))/eta) := by
      simpa only [ordinaryThresholdWeight,mul_div_assoc,mul_assoc] using
        mul_le_mul_of_nonneg_right hm hpos
    _ = gamma^(1/4:ℝ)*(eta^(-(1/2:ℝ))+eta^(-(11/20:ℝ))) := by rw [hpower]
    _ ≤ _ := by
      have h1 := Real.rpow_le_rpow_of_exponent_le heta (by norm_num : -(1/2:ℝ)≤ -(1/5:ℝ))
      have h2 := Real.rpow_le_rpow_of_exponent_le heta (by norm_num : -(11/20:ℝ)≤ -(1/5:ℝ))
      have hg := Real.rpow_nonneg hgamma.le (1/4:ℝ)
      nlinarith

end LipschitzHilbert

end

end OAI
