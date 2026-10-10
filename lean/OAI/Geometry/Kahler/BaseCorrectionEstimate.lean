import OAI.Geometry.Kahler.BaseCentralComparison

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def correctionModel (k : ℝ) (f b : ℝ → ℝ) (y S T : ℝ) (z : ℂ) : ℝ :=
  Real.exp (2*y/k)*(f y*S*z.re - b y/k*T*z.im)

lemma densityCorrectionRaw_model {k : ℕ} (hk : 0 < k) (f b : ℝ → ℝ) (W : Base → ℝ)
    (p : Sphere) {ξ : Base} (hξ : bracket ξ (p:Base) ≠ 0) :
    densityCorrectionRaw k f b W p ξ = correctionModel k f b (densityHeight k p ξ)
      (W (centralPoint p ξ)) (phaseDerivative W (centralPoint p ξ))
      ((bracket ξ (p:Base)/(‖bracket ξ (p:Base)‖:ℂ))^k) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have he : 2*densityHeight k p ξ/(k:ℝ) = -2*Real.log ‖bracket ξ (p:Base)‖ := by
    unfold densityHeight
    field_simp
  have hx : Real.exp (-2*Real.log ‖bracket ξ (p:Base)‖) = (‖bracket ξ (p:Base)‖^2)⁻¹ := by
    rw [show -2*Real.log ‖bracket ξ (p:Base)‖ = -(2*Real.log ‖bracket ξ (p:Base)‖) by ring,
      Real.exp_neg,show (2:ℝ) = (2:ℕ) by norm_num,
      Real.exp_nat_mul,Real.exp_log (norm_pos_iff.mpr hξ)]
  simp only [densityCorrectionRaw,correctionModel,he,hx]

lemma abs_sub_triangle (a b : ℝ) : |a-b| ≤ |a|+|b| := by
  simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)

lemma correctionModel_derivative_bound {k D F B F₁ B₁ : ℝ} (hk : 1 ≤ k) (hD : 0 ≤ D)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁)
    {f b y S T : ℝ → ℝ} {z : ℝ → ℂ} {t dy dS dT df db : ℝ} {dz : ℂ}
    (hy : HasDerivAt y dy t) (hS : HasDerivAt S dS t) (hT : HasDerivAt T dT t)
    (hz : HasDerivAt z dz t) (hf : HasDerivAt f df (y t)) (hb : HasDerivAt b db (y t))
    (hSp : 0 ≤ S t) (hyb : |dy| ≤ D) (hSb : |dS| ≤ D*S t) (hTb : |dT| ≤ D*k*S t)
    (hTv : |T t| ≤ k*S t) (hzv : ‖z t‖ ≤ 1) (hzb : ‖dz‖ ≤ D)
    (hfv : |f (y t)| ≤ F) (hbv : |b (y t)| ≤ B) (hfd : |df| ≤ F₁) (hbd : |db| ≤ B₁) :
    |deriv (fun u => correctionModel k f b (y u) (S u) (T u) (z u)) t| ≤
      D*Real.exp (2*y t/k)*S t*(4*(F+B)+F₁+B₁) := by
  have hk0 : 0 < k := by linarith
  have hzr : |(z t).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hzv
  have hzi : |(z t).im| ≤ 1 := (Complex.abs_im_le_norm _).trans hzv
  have hdr : |dz.re| ≤ D := (Complex.abs_re_le_norm _).trans hzb
  have hdi : |dz.im| ≤ D := (Complex.abs_im_le_norm _).trans hzb
  have hbdv : |b (y t)/k| ≤ B/k := by rw [abs_div,abs_of_pos hk0]; exact div_le_div_of_nonneg_right hbv hk0.le
  have hbdd : |db*dy/k| ≤ B₁*D/k := by rw [abs_div,abs_mul,abs_of_pos hk0]; gcongr
  have hfdd : |df*dy| ≤ F₁*D := by rw [abs_mul]; gcongr
  let H := f (y t)*S t*(z t).re-b (y t)/k*T t*(z t).im
  let dH := (df*dy*S t+f (y t)*dS)*(z t).re+f (y t)*S t*dz.re-
    ((db*dy/k*T t+b (y t)/k*dT)*(z t).im+b (y t)/k*T t*dz.im)
  have hH : |H| ≤ (F+B)*S t := by
    unfold H
    calc
      _ ≤ |f (y t)| * |S t| * |(z t).re| + |b (y t)/k| * |T t| * |(z t).im| := by
        simpa only [abs_mul] using abs_sub_triangle (f (y t)*S t*(z t).re) (b (y t)/k*T t*(z t).im)
      _ ≤ F*S t*1+(B/k)*(k*S t)*1 := by rw [abs_of_nonneg hSp]; gcongr
      _ = _ := by field_simp
  have hdH : |dH| ≤ D*S t*(2*(F+B)+F₁+B₁) := by
    unfold dH
    calc
      _ ≤ (|df*dy| * |S t| + |f (y t)| * |dS|)*|(z t).re| + |f (y t)| * |S t| * |dz.re| +
          ((|db*dy/k| * |T t| + |b (y t)/k| * |dT|)*|(z t).im| + |b (y t)/k| * |T t| * |dz.im|) := by
        apply (abs_sub_triangle _ _).trans
        apply add_le_add
        · apply (abs_add_le _ _).trans
          rw [abs_mul,abs_mul,abs_mul]
          gcongr
          simpa [abs_mul] using abs_add_le (df*dy*S t) (f (y t)*dS)
        · apply (abs_add_le _ _).trans
          rw [abs_mul,abs_mul,abs_mul]
          gcongr
          simpa [abs_mul] using abs_add_le (db*dy/k*T t) (b (y t)/k*dT)
      _ ≤ (F₁*D*S t+F*(D*S t))*1+F*S t*D+
          ((B₁*D/k*(k*S t)+(B/k)*(D*k*S t))*1+(B/k)*(k*S t)*D) := by
        rw [abs_of_nonneg hSp]
        gcongr
      _ = _ := by field_simp; ring
  have hex := ((hy.const_mul 2).div_const k).exp
  have hzrD := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
  have hziD := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
  have hprod := hex.mul (((hf.comp t hy).mul hS |>.mul hzrD).sub (((hb.comp t hy).div_const k).mul hT |>.mul hziD))
  have hder : deriv (fun u => correctionModel k f b (y u) (S u) (T u) (z u)) t =
      Real.exp (2*y t/k)*(2*dy/k)*H+Real.exp (2*y t/k)*dH := by
    convert! hprod.deriv using 1
  rw [hder]
  have he0 : 0 ≤ Real.exp (2*y t/k) := (Real.exp_pos _).le
  have hdy : |2*dy/k| ≤ 2*D/k := by rw [abs_div,abs_mul,abs_of_pos hk0]; norm_num; gcongr
  calc
    _ ≤ Real.exp (2*y t/k)*(2*D/k)*((F+B)*S t)+Real.exp (2*y t/k)*(D*S t*(2*(F+B)+F₁+B₁)) := by
      apply (abs_add_le _ _).trans
      simp only [abs_mul,abs_of_nonneg he0]
      gcongr
    _ ≤ Real.exp (2*y t/k)*(2*D)*((F+B)*S t)+Real.exp (2*y t/k)*(D*S t*(2*(F+B)+F₁+B₁)) := by
      gcongr
      exact div_le_self (by positivity) hk
    _ = _ := by ring

end PinchedHartogs.BaseConstruction

end

end OAI
