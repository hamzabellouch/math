import OAI.Geometry.RCD.Transport.RenyiDualScore

namespace OAI

/-! # Quantitative increase of the concave power under mass replacement

The replacement used in the midpoint construction moves mass out of a
superlevel set into a density bounded by the threshold. A strictly higher
superlevel set supplies a positive gap.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem rpow_increment_lower {q a b M : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbM : b ≤ M) (_hM : 0 < M) :
    q*M^(q-1)*(b-a) ≤ b^q-a^q := by
  by_cases hb : b=0
  · have ha0 : a=0 := le_antisymm (hab.trans_eq hb) ha
    simp [ha0,hb]
  have hb0 : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb)
  have ht := rpow_tangent_upper hb0 ha hq0 hq1
  have hp : b*b^(q-1)=b^q := by
    calc
      _ = b^(1:ℝ)*b^(q-1) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hb0]; congr 1; ring
  have hc := Real.rpow_le_rpow_of_nonpos hb0 hbM (by linarith : q-1 ≤ 0)
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hq0.le)
    (sub_nonneg.mpr hab)
  have hpq := congrArg (fun z : ℝ => q*z) hp
  nlinarith only [ht,hpq,hm]

theorem rpow_decrement_lower {q a b L : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hL : 0 < L) (hLb : L ≤ b) (hba : b ≤ a) :
    q*L^(q-1)*(b-a) ≤ b^q-a^q := by
  have hb0 := hL.trans_le hLb
  have ht := rpow_tangent_upper hb0 (hb0.le.trans hba) hq0 hq1
  have hp : b*b^(q-1)=b^q := by
    calc
      _ = b^(1:ℝ)*b^(q-1) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hb0]; congr 1; ring
  have hc := Real.rpow_le_rpow_of_nonpos hL hLb (by linarith : q-1 ≤ 0)
  have hm := mul_le_mul_of_nonpos_right (mul_le_mul_of_nonneg_left hc hq0.le)
    (sub_nonpos.mpr hba)
  have hpq := congrArg (fun z : ℝ => q*z) hp
  nlinarith only [ht,hpq,hm]

theorem renyiPerturb_low {q C a r h : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hC : 0 < C) (ha : 0 ≤ a) (hr : 0 ≤ r) (hrC : r ≤ C)
    (hh : 0 ≤ h) (hhC : h ≤ C) :
    a*q*(C*(1+a))^(q-1)*h ≤ (r+a*h)^q-r^q := by
  have hx := rpow_increment_lower hq0 hq1 hr
    (show r ≤ r+a*h by nlinarith) (show r+a*h ≤ C*(1+a) by nlinarith)
      (show 0 < C*(1+a) by positivity)
  nlinarith only [hx]

theorem renyiPerturb_high {q C a r h : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hC : 0 < C) (ha : 0 ≤ a) (ha1 : a < 1) (hCr : C ≤ r)
    (hh : 0 ≤ h) (hhC : h ≤ r) :
    a*q*((1-a)*C)^(q-1)*(h-r) ≤ ((1-a)*r+a*h)^q-r^q := by
  have hx := rpow_decrement_lower hq0 hq1
    (show 0 < (1-a)*C by positivity)
    (show (1-a)*C ≤ (1-a)*r+a*h by
      have h := mul_le_mul_of_nonneg_left hCr (by linarith : 0 ≤ 1-a)
      nlinarith)
    (show (1-a)*r+a*h ≤ r by nlinarith)
  nlinarith only [hx]

def renyiPerturbLower (q C D a r h : ℝ) : ℝ :=
  a*q*((C*(1+a))^(q-1)*h-((1-a)*C)^(q-1)*(if C<r then r else 0)+
    (((1-a)*C)^(q-1)-((1-a)*D)^(q-1))*(D-C)*(if D≤r then 1 else 0))

theorem renyiPerturb_power_lower {q C D a r h : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 < C) (hCD : C < D)
    (ha : 0 ≤ a) (ha1 : a < 1) (hr : 0 ≤ r) (hh : 0 ≤ h) (hhC : h ≤ C) :
    renyiPerturbLower q C D a r h ≤ (entropyPerturb C a r h)^q-r^q := by
  have hLC : 0 < (1-a)*C := by positivity
  have hq : q-1 ≤ 0 := by linarith
  have hcp : (C*(1+a))^(q-1) ≤ ((1-a)*C)^(q-1) :=
    Real.rpow_le_rpow_of_nonpos hLC (by nlinarith) hq
  have hcm : ((1-a)*D)^(q-1) ≤ ((1-a)*C)^(q-1) :=
    Real.rpow_le_rpow_of_nonpos hLC
      (mul_le_mul_of_nonneg_left hCD.le (by linarith)) hq
  have haq : 0 ≤ a*q := mul_nonneg ha hq0.le
  by_cases hCr : C<r
  · rw [entropyPerturb,ite_eq_left hCr]
    by_cases hDr : D≤r
    · have ht := renyiPerturb_high hq0 hq1 (hC.trans hCD) ha ha1 hDr hh (hhC.trans hCr.le)
      have hb : (C*(1+a))^(q-1)*h-((1-a)*C)^(q-1)*r+
          (((1-a)*C)^(q-1)-((1-a)*D)^(q-1))*(D-C) ≤
          ((1-a)*D)^(q-1)*(h-r) := by
        have h0 := mul_nonneg (sub_nonneg.mpr hcm) (show 0 ≤ r-h-(D-C) by linarith)
        have h1 := mul_nonneg (sub_nonneg.mpr hcp) hh
        nlinarith only [h0,h1]
      have hm := mul_le_mul_of_nonneg_left hb haq
      unfold renyiPerturbLower
      rw [ite_eq_left hCr,ite_eq_left hDr,mul_one]
      nlinarith only [hm,ht]
    · have ht := renyiPerturb_high hq0 hq1 hC ha ha1 hCr.le hh (hhC.trans hCr.le)
      have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcp hh) haq
      unfold renyiPerturbLower
      rw [ite_eq_left hCr,ite_eq_right hDr,mul_zero,add_zero]
      nlinarith only [hm,ht]
  · have hrC : r ≤ C := le_of_not_gt hCr
    have hDr : ¬D≤r := by linarith
    unfold renyiPerturbLower entropyPerturb
    simp only [ite_eq_right hCr,ite_eq_right hDr,mul_zero,sub_zero,add_zero]
    simpa only [mul_assoc] using renyiPerturb_low hq0 hq1 hC ha hr hrC hh hhC

end RegularPointCoordinates

end

end OAI
