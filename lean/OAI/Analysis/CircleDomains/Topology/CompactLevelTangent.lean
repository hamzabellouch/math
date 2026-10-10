import OAI.Analysis.CircleDomains.Topology.CompactTransverseField
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! A compactly supported smooth tangent field for an actual compact
regular planar level. This uses only the gradient of its defining scalar. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma complexScalarGradient_tangent (f : ℂ → ℝ) (z : ℂ) :
    (fderiv ℝ f z) (Complex.I * complexScalarGradient f z) = 0 := by
  rw [complexCovector_apply]
  simp only [complexScalarGradient,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

lemma complexScalarGradient_ne_zero {f : ℂ → ℝ} {z : ℂ} (hz : fderiv ℝ f z ≠ 0) :
    complexScalarGradient f z ≠ 0 := by
  intro h
  have hp := complexScalarGradient_positive hz
  rw [h,map_zero] at hp
  exact (lt_irrefl 0) hp

lemma exists_compact_level_tangent {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set ℂ} (hK : IsCompact K) (hregular : ∀ z ∈ K, fderiv ℝ f z ≠ 0) :
    ∃ (V : ℂ → ℂ) (L : ℝ≥0), ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      LipschitzWith L V ∧ (∀ z, (fderiv ℝ f z) (V z) = 0) ∧
      (∀ z ∈ K, V z ≠ 0) := by
  obtain ⟨χ,hχ,hc,_,_,hone⟩ :=
    exists_smooth_planar_cutoff hK isOpen_univ (subset_univ _)
  let V : ℂ → ℂ := fun z => χ z • (Complex.I * complexScalarGradient f z)
  have hs : ContDiff ℝ ∞ V := hχ.smul (contDiff_const.mul (complexScalarGradient_smooth hf))
  have hVc : HasCompactSupport V := hc.smul_right
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hs (by simp)
  refine ⟨V,L,hs,hVc,hL,?_,?_⟩
  · intro z
    simp only [V,map_smul,complexScalarGradient_tangent,smul_zero]
  · intro z hz
    have hχz := hone.self_of_nhdsSet z hz
    simp only [V,hχz,one_smul]
    exact mul_ne_zero Complex.I_ne_zero (complexScalarGradient_ne_zero (hregular z hz))

lemma integral_curve_preserves_scalar {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {V : ℂ → ℂ} (htangent : ∀ z, (fderiv ℝ f z) (V z) = 0)
    {γ : ℝ → ℂ} (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) (s t : ℝ) :
    f (γ s) = f (γ t) := by
  have hd (t : ℝ) : HasDerivAt (f ∘ γ) 0 t := by
    have h := (hf.differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    simpa only [htangent] using h
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

end CircleDomainRigidity

end

end OAI
