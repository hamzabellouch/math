import OAI.Analysis.CircleDomains.Sobolev.SmoothContours
import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorWedge
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! An explicit compactly supported smooth transverse field near a
compact regular scalar level, with a global Lipschitz bound. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

 def complexScalarGradient (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 : ℂ) + (fderiv ℝ f z Complex.I : ℂ) * Complex.I

lemma complexScalarGradient_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (complexScalarGradient f) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact (Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)).add
    ((Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)).mul contDiff_const)

lemma complexScalarGradient_positive {f : ℂ → ℝ} {z : ℂ}
    (hz : fderiv ℝ f z ≠ 0) : 0 < fderiv ℝ f z (complexScalarGradient f z) := by
  have he : fderiv ℝ f z (complexScalarGradient f z) =
      (fderiv ℝ f z 1)^2 + (fderiv ℝ f z Complex.I)^2 := by
    rw [complexCovector_apply]
    simp only [complexScalarGradient, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [he]
  have hn : fderiv ℝ f z 1 ≠ 0 ∨ fderiv ℝ f z Complex.I ≠ 0 := by
    by_contra! hc
    apply hz
    ext v
    rw [complexCovector_apply, hc.1, hc.2]
    simp
  rcases hn with hn | hn <;> nlinarith [sq_pos_of_ne_zero hn,
    sq_nonneg (fderiv ℝ f z 1), sq_nonneg (fderiv ℝ f z Complex.I)]

lemma exists_compact_transverse_field {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set ℂ} (hK : IsCompact K) (hregular : ∀ z ∈ K, fderiv ℝ f z ≠ 0) :
    ∃ (V : ℂ → ℂ) (L : ℝ≥0), ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      LipschitzWith L V ∧ ∀ z ∈ K, 0 < fderiv ℝ f z (V z) := by
  obtain ⟨χ, hχ, hc, _, _, hone⟩ :=
    exists_smooth_planar_cutoff hK isOpen_univ (subset_univ _)
  let V : ℂ → ℂ := fun z => χ z • complexScalarGradient f z
  have hs : ContDiff ℝ ∞ V := hχ.smul (complexScalarGradient_smooth hf)
  have hVc : HasCompactSupport V := hc.smul_right
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hs (by simp)
  refine ⟨V, L, hs, hVc, hL, ?_⟩
  intro z hz
  have hχz := hone.self_of_nhdsSet z hz
  simpa only [V, hχz, one_smul] using complexScalarGradient_positive (hregular z hz)

end CircleDomainRigidity

end

end OAI
