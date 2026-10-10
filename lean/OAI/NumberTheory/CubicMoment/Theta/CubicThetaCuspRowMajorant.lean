import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinBounds

namespace OAI

/-! A uniform denominator bound for nonconstant rows in any integral
cusp. This bound is independent of the congruence class of the row. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCuspRowDenominator (c d : Eisenstein) (z : ℂ) (v : ℝ) : ℝ :=
  Complex.normSq ((c:ℂ)*z+d)+norm c*v^2

lemma cubicThetaCuspRowDenominator_lower (c d : Eisenstein) (z : ℂ) (v : ℝ) :
    norm c*v^2≤cubicThetaCuspRowDenominator c d z v := by
  exact le_add_of_nonneg_left (Complex.normSq_nonneg _)

lemma cubicThetaCuspRowDenominator_pos {c : Eisenstein} (hc : c≠0)
    (d : Eisenstein) (z : ℂ) {v : ℝ} (hv : 0<v) :
    0<cubicThetaCuspRowDenominator c d z v :=
  (mul_pos (norm_pos_of_ne_zero hc) (sq_pos_of_pos hv)).trans_le
    (cubicThetaCuspRowDenominator_lower c d z v)

lemma cubicThetaCuspRowDenominator_horizontal {c : Eisenstein} (hc : c≠0)
    (d : Eisenstein) (z : ℂ) {v R : ℝ} (hv : 1≤v) (hz : Complex.normSq z≤R) :
    1+norm d≤(3+2*R)*cubicThetaCuspRowDenominator c d z v := by
  let D := cubicThetaCuspRowDenominator c d z v
  have hD : norm c*v^2≤D := cubicThetaCuspRowDenominator_lower c d z v
  have hc0 := norm_nonneg c
  have hcv : norm c≤D := (le_mul_of_one_le_right hc0 (by nlinarith : 1≤v^2)).trans hD
  have hD0 : 0≤D := hc0.trans hcv
  have hR : 0≤R := (Complex.normSq_nonneg z).trans hz
  have hs : Complex.normSq (((c:ℂ)*z+d)-((c:ℂ)*z))≤
      2*Complex.normSq ((c:ℂ)*z+d)+2*Complex.normSq ((c:ℂ)*z) := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    nlinarith [sq_nonneg (((c:ℂ)*z+d).re+((c:ℂ)*z).re),
      sq_nonneg (((c:ℂ)*z+d).im+((c:ℂ)*z).im)]
  rw [add_sub_cancel_left,Complex.normSq_mul] at hs
  change norm d≤2*Complex.normSq ((c:ℂ)*z+d)+2*(norm c*Complex.normSq z) at hs
  have hprod : norm c*Complex.normSq z≤D*R :=
    mul_le_mul hcv hz (Complex.normSq_nonneg z) hD0
  have hsq : Complex.normSq ((c:ℂ)*z+d)≤D :=
    le_add_of_nonneg_right (mul_nonneg hc0 (sq_nonneg v))
  have hd : norm d≤2*D+2*(D*R) := by
    nlinarith
  have hD1 : 1≤D := (one_le_norm hc).trans hcv
  nlinarith

lemma cubicThetaCuspRowHeight_power {c : Eisenstein} (hc : c≠0)
    (d : Eisenstein) (z : ℂ) {v R σ : ℝ} (hv : 1≤v) (hz : Complex.normSq z≤R)
    (hσ : 2≤σ) :
    (v/cubicThetaCuspRowDenominator c d z v)^σ≤
      (3+2*R)^2*v^(4-σ)*norm c^(-(σ-2))*(1+norm d)^(-2:ℝ) := by
  have hv0 : 0<v := lt_of_lt_of_le zero_lt_one hv
  have hc0 := norm_pos_of_ne_zero hc
  have hD := cubicThetaCuspRowDenominator_pos hc d z hv0
  have hR : 0≤R := (Complex.normSq_nonneg z).trans hz
  have hC : 0<3+2*R := by linarith
  have hd : 0<1+norm d := by linarith [norm_nonneg d]
  have hlo : (1+norm d)/(3+2*R)≤cubicThetaCuspRowDenominator c d z v :=
    (div_le_iff₀ hC).mpr (by
      simpa only [mul_comm] using cubicThetaCuspRowDenominator_horizontal hc d z hv hz)
  have h₁ := Real.rpow_le_rpow_of_nonpos (mul_pos hc0 (sq_pos_of_pos hv0))
    (cubicThetaCuspRowDenominator_lower c d z v) (by linarith : -(σ-2)≤0)
  have h₂ := Real.rpow_le_rpow_of_nonpos (div_pos hd hC) hlo (by norm_num : (-2:ℝ)≤0)
  have hs : (cubicThetaCuspRowDenominator c d z v)^(-σ)=
      (cubicThetaCuspRowDenominator c d z v)^(-(σ-2))*
        (cubicThetaCuspRowDenominator c d z v)^(-2:ℝ) := by
    rw [← Real.rpow_add hD]
    congr 1
    ring
  have he₂ : ((1+norm d)/(3+2*R))^(-2:ℝ)=
      (3+2*R)^2*(1+norm d)^(-2:ℝ) := by
    rw [Real.div_rpow hd.le hC.le]
    simp only [Real.rpow_neg hd.le,Real.rpow_neg hC.le,Real.rpow_two]
    field_simp [hd.ne',hC.ne']
  have he₁ : v^σ*(v^2)^(-(σ-2))=v^(4-σ) := by
    rw [← Real.rpow_natCast_mul hv0.le,← Real.rpow_add hv0]
    congr 1
    push_cast
    ring
  calc
    _ = v^σ*(cubicThetaCuspRowDenominator c d z v)^(-σ) := by
      rw [Real.div_rpow hv0.le hD.le,Real.rpow_neg hD.le,div_eq_mul_inv]
    _ = v^σ*((cubicThetaCuspRowDenominator c d z v)^(-(σ-2))*
        (cubicThetaCuspRowDenominator c d z v)^(-2:ℝ)) := by rw [hs]
    _ ≤ v^σ*((norm c*v^2)^(-(σ-2))*((1+norm d)/(3+2*R))^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂
        (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (mul_pos hc0 (sq_pos_of_pos hv0)).le _))
        (Real.rpow_nonneg hv0.le _)
    _ = _ := by
      rw [Real.mul_rpow hc0.le (sq_nonneg v),he₂]
      calc
        _ = (3+2*R)^2*(v^σ*(v^2)^(-(σ-2)))*norm c^(-(σ-2))*(1+norm d)^(-2:ℝ) := by ring
        _ = _ := by rw [he₁]

end CubicFirstMoment

end

end OAI
