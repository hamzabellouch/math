import OAI.Analysis.CircleDomains.Modulus.FiniteWeightedCutoffs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! Dirichlet energy of a smooth planar cutoff is unchanged by dilation.
This supplies the fixed energy budget for disjoint concentric transition
annuli used to make cutoffs of arbitrarily small energy. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def dilatedCutoff (f : ℂ → ℝ) (r : ℝ) : ℂ → ℝ := fun z => f (r⁻¹ • z)

 theorem dilatedCutoff_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    ContDiff ℝ ∞ (dilatedCutoff f r) := hf.comp (contDiff_id.const_smul _)

 theorem dilatedCutoff_compact {f : ℂ → ℝ} (hs : HasCompactSupport f)
    {r : ℝ} (hr : r ≠ 0) : HasCompactSupport (dilatedCutoff f r) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero hr)).unit
  exact hs.comp_homeomorph e

 theorem dilatedCutoff_fderiv {f : ℂ → ℝ} (hf : Differentiable ℝ f) (r : ℝ) (z : ℂ) :
    fderiv ℝ (dilatedCutoff f r) z = r⁻¹ • fderiv ℝ f (r⁻¹ • z) := by
  have hd := (hf (r⁻¹ • z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul r⁻¹)
  change fderiv ℝ (f ∘ fun w : ℂ => r⁻¹ • w) z = _
  rw [hd.fderiv]
  ext w
  simp

 theorem smooth_cutoff_energy_integrable {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Integrable (fun z => ‖fderiv ℝ f z‖^2) := by
  have hd : Continuous (fderiv ℝ f) :=
    (hf.fderiv_right (m := (↑(⊤ : ℕ∞))) (by simp)).continuous
  apply (hd.norm.pow 2).integrable_of_hasCompactSupport
  apply (hs.fderiv (𝕜 := ℝ)).mono'
  intro z hz
  by_contra hzero
  apply hz
  change ‖fderiv ℝ f z‖^2 = 0
  simp only [image_eq_zero_of_notMem_tsupport hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

 theorem dilatedCutoff_energy {f : ℂ → ℝ} (hf : Differentiable ℝ f)
    {r : ℝ} (hr : 0 < r) :
    (∫ z, ‖fderiv ℝ (dilatedCutoff f r) z‖^2) = ∫ z, ‖fderiv ℝ f z‖^2 := by
  simp_rw [dilatedCutoff_fderiv hf, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr), mul_pow]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun z : ℂ => ‖fderiv ℝ f z‖^2) hr.le]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  field_simp

end CircleDomainRigidity

end

end OAI
