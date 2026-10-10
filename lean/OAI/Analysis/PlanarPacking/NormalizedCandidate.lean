import OAI.Analysis.PlanarPacking.Basic
import OAI.Analysis.PlanarPacking.Dilation
import OAI.Analysis.PlanarPacking.OriginPositive

namespace OAI

/-! # Normalization of the radial Schwartz Fourier pair -/

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def normalizationConstant : ℝ := (b*exactLeft 0)⁻¹
lemma normalizationConstant_pos : 0<normalizationConstant := inv_pos.mpr (mul_pos b_pos exactLeft_origin_positive)
noncomputable def normalizedCandidate : SchwartzMap Plane ℝ :=
  normalizationConstant • dilateSchwartz exactLeft scaleFactor scaleFactor_pos.ne'
lemma normalizedCandidate_apply (x : Plane) :
    normalizedCandidate x=normalizationConstant*exactLeft (scaleFactor • x) := rfl
lemma exactLeft_radial : Radial exactLeft := by
  intro x y hxy
  rw [exactLeft_apply,exactLeft_apply,hxy]
lemma normalizedCandidate_radial : Radial normalizedCandidate := by
  intro x y hxy
  simp only [normalizedCandidate_apply]
  rw [exactLeft_radial (scaleFactor • x) (scaleFactor • y) (by simp only [norm_smul,hxy])]
lemma normalizedCandidate_origin : normalizedCandidate 0=2/Real.sqrt 3 := by
  rw [normalizedCandidate_apply,smul_zero]
  unfold normalizationConstant
  have hb := b_pos.ne'
  have he := exactLeft_origin_positive.ne'
  simp only [b]
  field_simp
lemma fourier_eq_fourierIntegral (f : Plane→ℝ) (ξ : Plane) :
    fourier f ξ=𝓕 (fun x : Plane => (f x:ℂ)) ξ := by
  rw [fourier,Real.fourier_eq']
  simp only [smul_eq_mul]
  congr 1
  funext x
  ring
lemma normalizedCandidate_fourier (ξ : Plane) :
    fourier normalizedCandidate ξ=(exactRight (scaleFactor⁻¹ • ξ)/exactLeft 0:ℝ) := by
  rw [fourier_eq_fourierIntegral]
  change 𝓕 (fun x : Plane => ((normalizationConstant * exactLeft (scaleFactor • x):ℝ):ℂ)) ξ=_
  rw [plane_fourier_real_const,plane_fourier_dilation (fun x : Plane => (exactLeft x:ℂ)) scaleFactor_pos.ne',scaleFactor_inv_sq]
  rw [show 𝓕 (fun x : Plane => (exactLeft x:ℂ)) (scaleFactor⁻¹ • ξ)=
    (exactRight (scaleFactor⁻¹ • ξ):ℂ) from pair_fourier exactData₁ exactData₂ _]
  simp only [Complex.real_smul,← Complex.ofReal_mul,Complex.ofReal_inj]
  unfold normalizationConstant
  field_simp [b_pos.ne',exactLeft_origin_positive.ne']
lemma normalizedCandidate_fourier_origin : fourier normalizedCandidate 0=1 := by
  rw [normalizedCandidate_fourier,smul_zero,← exact_origin_identity,div_self exactLeft_origin_positive.ne']
  norm_num
lemma normalizedCandidate_fourier_real (ξ : Plane) : (fourier normalizedCandidate ξ).im=0 := by
  rw [normalizedCandidate_fourier]; rfl
end SharpPlanar

end OAI
