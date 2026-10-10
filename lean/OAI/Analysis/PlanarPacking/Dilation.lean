import OAI.Analysis.PlanarPacking.Cardinal
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def scaleEquiv (a : ℝ) (ha : a≠0) : Plane ≃L[ℝ] Plane where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℝ Plane a ha
  continuous_toFun := continuous_const_smul a
  continuous_invFun := continuous_const_smul a⁻¹
noncomputable def dilateSchwartz (f : SchwartzMap Plane ℝ) (a : ℝ) (ha : a≠0) : SchwartzMap Plane ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (scaleEquiv a ha) f
lemma dilateSchwartz_apply (f : SchwartzMap Plane ℝ) (a : ℝ) (ha : a≠0) (x : Plane) :
    dilateSchwartz f a ha x=f (a • x) := rfl
lemma plane_fourier_dilation (f : Plane→ℂ) {a : ℝ} (ha : a≠0) (ξ : Plane) :
    𝓕 (fun x : Plane => f (a • x)) ξ=(a^2)⁻¹ • 𝓕 f (a⁻¹ • ξ) := by
  let G : Plane→ℂ := fun x => Complex.exp (((-2*Real.pi*inner ℝ x (a⁻¹ • ξ):ℝ):ℂ)*Complex.I)*f x
  have he : (fun x : Plane => Complex.exp (((-2*Real.pi*inner ℝ x ξ:ℝ):ℂ)*Complex.I)*f (a • x))=
      fun x => G (a • x) := by
    funext x
    dsimp [G]
    rw [real_inner_smul_left,real_inner_smul_right]
    have hh : a*(a⁻¹*inner ℝ x ξ)=inner ℝ x ξ := by field_simp
    rw [hh]
  rw [Real.fourier_eq',Real.fourier_eq']
  simp only [smul_eq_mul]
  rw [he,Measure.integral_comp_smul]
  have hd : Module.finrank ℝ Plane=2 := by simp [Plane]
  rw [hd,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg a))]
lemma plane_fourier_real_const (f : Plane→ℝ) (c : ℝ) (ξ : Plane) :
    𝓕 (fun x : Plane => ((c*f x:ℝ):ℂ)) ξ=(c:ℂ)*𝓕 (fun x : Plane => (f x:ℂ)) ξ := by
  simp only [Real.fourier_eq',Complex.ofReal_mul,smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring
noncomputable def scaleFactor : ℝ := (Real.sqrt b)⁻¹
lemma scaleFactor_pos : 0<scaleFactor := inv_pos.mpr (Real.sqrt_pos.mpr b_pos)
lemma scaleFactor_sq : scaleFactor^2=b⁻¹ := by rw [scaleFactor,inv_pow,Real.sq_sqrt b_pos.le]
lemma scaled_radius (x : Plane) : b*‖scaleFactor • x‖^2=‖x‖^2 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos scaleFactor_pos,mul_pow,scaleFactor_sq]
  field_simp [b_pos.ne']
lemma scaleFactor_inv_sq : (scaleFactor^2)⁻¹=b := by rw [scaleFactor_sq,inv_inv]
end SharpPlanar

end OAI
