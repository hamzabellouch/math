import OAI.Geometry.Relativity.CKS.CollarMetricRealization
import OAI.Geometry.Relativity.CKS.AreaCuts

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise

def originalMetricCorrection (z : ℝ) (mg : Mat) (mr : ℝ) (eg : Mat) (err : ℝ) (b : Point) : AmbientMat :=
  metricBlock ((1+z^2)*(mr+z*err)) (fun a => Real.sqrt (1+z^2)*b a) (mg+z • eg)

lemma originalMetricCorrection_bound {B z mr err : ℝ} {mg eg : Mat} {b : Point}
    (hB : 0 ≤ B) (hz : |z| ≤ 1) (hmr : |mr| ≤ B) (herr : |err| ≤ B)
    (hmg : ‖mg‖ ≤ B) (heg : ‖eg‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖originalMetricCorrection z mg mr eg err b‖ ≤ 4*B := by
  have hz2 : z^2 ≤ 1 := by nlinarith [sq_abs z, abs_nonneg z]
  have hs : Real.sqrt (1+z^2) ≤ 2 := by
    have hh := Real.sq_sqrt (show 0 ≤ 1+z^2 by positivity)
    have hh' := Real.sqrt_nonneg (1+z^2)
    nlinarith
  have hr : |(1+z^2)*(mr+z*err)| ≤ 4*B := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ 1+z^2 by positivity)]
    have hh : |mr+z*err| ≤ 2*B := by
      calc |mr+z*err| ≤ |mr|+|z*err| := abs_add_le _ _
           _ = |mr|+|z| * |err| := by rw [abs_mul]
           _ ≤ B+1*B := add_le_add hmr (mul_le_mul hz herr (abs_nonneg _) (by norm_num))
           _ = 2*B := by ring
    exact (mul_le_mul (by linarith : 1+z^2 ≤ 2) hh (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hmix (a : Fin 2) : |Real.sqrt (1+z^2)*b a| ≤ 4*B := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    have ha : |b a| ≤ B := (norm_le_pi_norm b a).trans hb
    nlinarith [mul_le_mul hs ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
  have hleaf (a c : Fin 2) : |mg a c+z*eg a c| ≤ 4*B := by
    have hm : |mg a c| ≤ B := ((norm_le_pi_norm (mg a) c).trans (norm_le_pi_norm mg a)).trans hmg
    have he : |eg a c| ≤ B := ((norm_le_pi_norm (eg a) c).trans (norm_le_pi_norm eg a)).trans heg
    calc |mg a c+z*eg a c| ≤ |mg a c|+|z*eg a c| := abs_add_le _ _
         _ = |mg a c|+|z| * |eg a c| := by rw [abs_mul]
         _ ≤ B+1*B := add_le_add hm (mul_le_mul hz he (abs_nonneg _) (by norm_num))
         _ ≤ 4*B := by linarith
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro j
  fin_cases i <;> fin_cases j <;>
    simpa only [originalMetricCorrection,metricBlock,Matrix.of_apply,Real.norm_eq_abs,
      Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.head_fin_const] using
      (by first | exact hr | exact hmix 0 | exact hmix 1 | exact hleaf 0 0 |
        exact hleaf 0 1 | exact hleaf 1 0 | exact hleaf 1 1)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSAngularGeometry
open scoped Matrix.Norms.Elementwise

lemma ScaledComponentBound.value {f : Point → ℝ} {j q : ℕ} {B : ℝ} {y : Point}
    (h : ScaledComponentBound f j q B y) : |f y| ≤ B/(y 0)^q := by
  exact h [] (Nat.zero_le _)

lemma scaled_value_bound {r v B : ℝ} {n : ℕ} (hr : 0<r) (h : |v| ≤ B/r^n) :
    |r^n*v| ≤ B := by
  rw [abs_mul,abs_of_pos (pow_pos hr n)]
  simpa only [mul_comm] using (le_div_iff₀ (pow_pos hr n)).mp h

lemma originalMetric_factor {f : SourceMassFields} {y : Point} (hy : 0<y 0) :
    radialNormalize (y 0) (sourceMetric f y)-metricBlock 1 0 (f.sigma (angularProjection y)) =
      (1/(y 0))^3 • originalMetricCorrection (1/(y 0)) (f.mg (angularProjection y))
        (f.mr (angularProjection y)) ((y 0)^2 • f.eg y) ((y 0)^6*f.err y) ((y 0)^3 • f.b y) := by
  have hr := hy.ne'
  have hs : Real.sqrt (1+(y 0)^2)=(y 0)*Real.sqrt (1+(1/(y 0))^2) := by
    have he : 1+(y 0)^2=(y 0)^2*(1+(1/(y 0))^2) := by field_simp; ring
    rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hy.le]
  have hsq : Real.sqrt (1+(1/(y 0))^2)^2=1+(1/(y 0))^2 := Real.sq_sqrt (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialNormalize,radialScale,sourceMetric,sourceRadialMetric,sourceGamma,
      originalMetricCorrection,metricBlock,Matrix.of_apply,hs]
  all_goals try field_simp
  all_goals try rw [Real.sq_sqrt (show 0 ≤ ((y 0)^2+1)/(y 0)^2 by positivity)]
  all_goals try field_simp
  all_goals ring

theorem originalMetric_error {f : SourceMassFields} {y : Point} {B : ℝ}
    (hy : 1 ≤ y 0) (hB : 0 ≤ B) (hmr : |f.mr (angularProjection y)| ≤ B)
    (hmg : ‖f.mg (angularProjection y)‖ ≤ B) (hb : f.ComponentBounds B y) :
    ‖radialNormalize (y 0) (sourceMetric f y)-metricBlock 1 0 (f.sigma (angularProjection y))‖ ≤
      4*B/(y 0)^3 := by
  have hr : 0<y 0 := zero_lt_one.trans_le hy
  have hz : |1/(y 0)| ≤ 1 := by rw [abs_of_pos (one_div_pos.mpr hr)]; exact (div_le_one hr).mpr hy
  have heg : ‖(y 0)^2 • f.eg y‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
    apply (pi_norm_le_iff_of_nonneg hB).mpr; intro c
    exact scaled_value_bound hr (hb.eg a c).value
  have hbb : ‖(y 0)^3 • f.b y‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
    exact scaled_value_bound hr (hb.b a).value
  have herr := scaled_value_bound hr hb.err.value
  rw [originalMetric_factor hr,norm_smul,Real.norm_eq_abs,abs_pow,abs_of_pos (one_div_pos.mpr hr)]
  calc (1/y 0)^3* ‖originalMetricCorrection (1/y 0) (f.mg (angularProjection y))
          (f.mr (angularProjection y)) ((y 0)^2 • f.eg y) ((y 0)^6*f.err y) ((y 0)^3 • f.b y)‖
      ≤ (1/y 0)^3*(4*B) := mul_le_mul_of_nonneg_left
        (originalMetricCorrection_bound hB hz hmr herr hmg heg hbb) (by positivity)
    _ = 4*B/(y 0)^3 := by ring

end
end CKSMixedGeometry

end

end OAI
