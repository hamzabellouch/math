import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! # A common density gives a strict oscillation bound for weighted means

This is the scalar estimate for the derivative of two positive-kernel
log transforms. All densities and products are integrated explicitly.
-/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

theorem weighted_mean_minorization {r w f : Y → ℝ} {q l u : ℝ}
    (hr : Integrable r μ) (hw : Integrable w μ)
    (hfr : Integrable (fun x => f x*r x) μ) (hfw : Integrable (fun x => f x*w x) μ)
    (hr1 : (∫ x, r x ∂μ)=1) (hw1 : (∫ x, w x ∂μ)=1)
    (hmin : ∀ᵐ x ∂μ, q*r x ≤ w x) (hf : ∀ᵐ x ∂μ, l ≤ f x ∧ f x ≤ u) :
    q*(∫ x, f x*r x ∂μ)+(1-q)*l ≤ ∫ x, f x*w x ∂μ ∧
      (∫ x, f x*w x ∂μ) ≤ q*(∫ x, f x*r x ∂μ)+(1-q)*u := by
  let d := fun x => w x-q*r x
  have hd : Integrable d μ := hw.sub (hr.const_mul q)
  have hfd : Integrable (fun x => f x*d x) μ := by
    convert hfw.sub (hfr.const_mul q) using 1
    funext x
    change f x * (w x - q * r x) = f x * w x - q * (f x * r x)
    ring
  have hdint : (∫ x, d x ∂μ)=1-q := by
    rw [integral_sub hw (hr.const_mul q),integral_const_mul,hr1,hw1,mul_one]
  have hfdint : (∫ x, f x*d x ∂μ) = (∫ x, f x*w x ∂μ)-q*(∫ x, f x*r x ∂μ) := by
    have he : (fun x => f x*d x) = (fun x => f x*w x - q*(f x*r x)) := by
      funext x
      dsimp only [d]
      ring
    rw [he,integral_sub hfw (hfr.const_mul q),integral_const_mul]
  have hlo : (∫ x, l*d x ∂μ) ≤ ∫ x, f x*d x ∂μ := by
    apply integral_mono_ae (hd.const_mul l) hfd
    filter_upwards [hmin,hf] with x hx hf
    exact mul_le_mul_of_nonneg_right hf.1 (sub_nonneg.mpr hx)
  have hhi : (∫ x, f x*d x ∂μ) ≤ ∫ x, u*d x ∂μ := by
    apply integral_mono_ae hfd (hd.const_mul u)
    filter_upwards [hmin,hf] with x hx hf
    exact mul_le_mul_of_nonneg_right hf.2 (sub_nonneg.mpr hx)
  rw [integral_const_mul,hdint,hfdint] at hlo hhi
  constructor <;> linarith only [hlo,hhi]

theorem common_density_mean_difference {r w v f : Y → ℝ} {q l u : ℝ}
    (hr : Integrable r μ) (hw : Integrable w μ) (hv : Integrable v μ)
    (hfr : Integrable (fun x => f x*r x) μ) (hfw : Integrable (fun x => f x*w x) μ)
    (hfv : Integrable (fun x => f x*v x) μ)
    (hr1 : (∫ x, r x ∂μ)=1) (hw1 : (∫ x, w x ∂μ)=1) (hv1 : (∫ x, v x ∂μ)=1)
    (hwmin : ∀ᵐ x ∂μ, q*r x ≤ w x) (hvmin : ∀ᵐ x ∂μ, q*r x ≤ v x)
    (hf : ∀ᵐ x ∂μ, l ≤ f x ∧ f x ≤ u) :
    |(∫ x, f x*w x ∂μ)-(∫ x, f x*v x ∂μ)| ≤ (1-q)*(u-l) := by
  have hW := weighted_mean_minorization μ hr hw hfr hfw hr1 hw1 hwmin hf
  have hV := weighted_mean_minorization μ hr hv hfr hfv hr1 hv1 hvmin hf
  apply abs_le.mpr
  constructor <;> nlinarith only [hW.1,hW.2,hV.1,hV.2]

end RegularPointCoordinates

end

end OAI
