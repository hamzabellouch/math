import OAI.Geometry.SurfaceImmersion.Geometry.MetricGaussInvariance
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

/-! At a zero of a nonnegative smooth amplitude, its square has zero two-jet.
Thus adding the primitive metric does not change the boundary Gauss scalar. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes

private lemma scalar_partial_smooth {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) (v : Base) :
    ContDiff ℝ ∞ (coordDeriv v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private lemma scalar_partial_mul {f g : Base → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v p : Base) :
    coordDeriv v (fun x => f x*g x) p = coordDeriv v f p*g p+f p*coordDeriv v g p := by
  unfold coordDeriv
  rw [fderiv_fun_mul (hf.differentiable (by simp) p) (hg.differentiable (by simp) p)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

private lemma scalar_partial_add {f g : Base → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v p : Base) :
    coordDeriv v (fun x => f x+g x) p = coordDeriv v f p+coordDeriv v g p := by
  unfold coordDeriv
  rw [fderiv_fun_add (hf.differentiable (by simp) p) (hg.differentiable (by simp) p)]
  rfl

lemma square_twoJet_zero {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) {p : Base}
    (hzero : a p = 0) (hnonneg : ∀ᶠ q in 𝓝 p, 0 ≤ a q) :
    (fun q => (a q)^2) p = 0 ∧
      (∀ v, coordDeriv v (fun q => (a q)^2) p = 0) ∧
      ∀ v w, coordDeriv v (coordDeriv w (fun q => (a q)^2)) p = 0 := by
  have hmin : IsLocalMin a p := by simpa only [IsLocalMin,IsMinFilter,hzero] using hnonneg
  have hda : fderiv ℝ a p = 0 := hmin.fderiv_eq_zero
  have hd (v : Base) : coordDeriv v a p = 0 := by simp [coordDeriv,hda]
  have heq (w : Base) : coordDeriv w (fun q => (a q)^2) =
      fun q => coordDeriv w a q*a q+a q*coordDeriv w a q := by
    funext q
    simpa only [pow_two] using scalar_partial_mul ha ha w q
  refine ⟨by simp [hzero],?_,?_⟩
  · intro v
    rw [heq]
    simp [hzero]
  · intro v w
    rw [heq,scalar_partial_add ((scalar_partial_smooth ha w).mul ha)
      (ha.mul (scalar_partial_smooth ha w)),
      scalar_partial_mul (scalar_partial_smooth ha w) ha,
      scalar_partial_mul ha (scalar_partial_smooth ha w)]
    simp [hzero,hd]

lemma coordinateGauss_add_square_boundary {E F G a : Base → ℝ}
    (hE : ContDiff ℝ ∞ E) (ha : ContDiff ℝ ∞ a) {p : Base}
    (hzero : a p = 0) (hnonneg : ∀ᶠ q in 𝓝 p, 0 ≤ a q) :
    coordinateGauss (fun q => E q+(a q)^2) F G p = coordinateGauss E F G p := by
  obtain ⟨hz,hd,hdd⟩ := square_twoJet_zero ha hzero hnonneg
  have hsq : ContDiff ℝ ∞ (fun q => (a q)^2) := ha.pow 2
  have hfirst (v : Base) : coordDeriv v (fun q => E q+(a q)^2) =
      fun q => coordDeriv v E q+coordDeriv v (fun q => (a q)^2) q := by
    funext q
    exact scalar_partial_add hE hsq v q
  have hsecond (v w : Base) : coordDeriv v (coordDeriv w (fun q => E q+(a q)^2)) p =
      coordDeriv v (coordDeriv w E) p := by
    rw [hfirst,scalar_partial_add (scalar_partial_smooth hE w)
      (scalar_partial_smooth hsq w),hdd,add_zero]
  unfold coordinateGauss
  rw [hsecond]
  simp only [hfirst,hd,hzero,zero_pow (by decide : 2 ≠ 0),add_zero]

lemma factor_square_twoJet_zero {a f : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hf : ContDiff ℝ ∞ f) {p : Base} (hzero : a p = 0)
    (hnonneg : ∀ᶠ q in 𝓝 p, 0 ≤ a q) :
    (fun q => f q*(a q)^2) p = 0 ∧
      (∀ v, coordDeriv v (fun q => f q*(a q)^2) p = 0) ∧
      ∀ v w, coordDeriv v (coordDeriv w (fun q => f q*(a q)^2)) p = 0 := by
  obtain ⟨hz,hd,hdd⟩ := square_twoJet_zero ha hzero hnonneg
  have hsq : ContDiff ℝ ∞ (fun q => (a q)^2) := ha.pow 2
  have heq (w : Base) : coordDeriv w (fun q => f q*(a q)^2) =
      fun q => coordDeriv w f q*(a q)^2+f q*coordDeriv w (fun q => (a q)^2) q := by
    funext q
    exact scalar_partial_mul hf hsq w q
  refine ⟨by simp [hzero],?_,?_⟩
  · intro v
    rw [heq]
    simp only [hz,hd,mul_zero,add_zero]
  · intro v w
    rw [heq,scalar_partial_add ((scalar_partial_smooth hf w).mul hsq)
      (hf.mul (scalar_partial_smooth hsq w)),
      scalar_partial_mul (scalar_partial_smooth hf w) hsq,
      scalar_partial_mul hf (scalar_partial_smooth hsq w)]
    simp only [hz,hd,hdd,mul_zero,add_zero]

lemma coordinateGauss_add_factor_square_boundary {E F G a f : Base → ℝ}
    (hE : ContDiff ℝ ∞ E) (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) {p : Base}
    (hzero : a p = 0) (hnonneg : ∀ᶠ q in 𝓝 p, 0 ≤ a q) :
    coordinateGauss (fun q => E q+f q*(a q)^2) F G p = coordinateGauss E F G p := by
  obtain ⟨hz,hd,hdd⟩ := factor_square_twoJet_zero ha hf hzero hnonneg
  have hsq : ContDiff ℝ ∞ (fun q => f q*(a q)^2) := hf.mul (ha.pow 2)
  have hfirst (v : Base) : coordDeriv v (fun q => E q+f q*(a q)^2) =
      fun q => coordDeriv v E q+coordDeriv v (fun q => f q*(a q)^2) q := by
    funext q
    exact scalar_partial_add hE hsq v q
  have hsecond (v w : Base) : coordDeriv v (coordDeriv w (fun q => E q+f q*(a q)^2)) p =
      coordDeriv v (coordDeriv w E) p := by
    rw [hfirst,scalar_partial_add (scalar_partial_smooth hE w)
      (scalar_partial_smooth hsq w),hdd,add_zero]
  unfold coordinateGauss
  rw [hsecond]
  simp only [hfirst,hd,hz,add_zero]

end ClosedSurfaceR4.RealModes

end

end OAI
