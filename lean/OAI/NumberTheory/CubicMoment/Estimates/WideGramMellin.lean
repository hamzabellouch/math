import OAI.NumberTheory.CubicGram.MellinNorm

namespace OAI

/-! Exact Mellin separation on the entire fixed norm range of a prime
convolution. The cutoff belongs to the transform, so no cutoff is inserted
into the arithmetic coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

def wideGramLogBump (M : ℝ) (hM : 0 < M) : ContDiffBump (0:ℝ) :=
  ⟨M,2*M,hM,by linarith⟩

def wideGramLogKernel (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (ρ u : ℝ) : ℂ :=
  wideGramLogBump M hM u • normProfileFourier W ((Real.sqrt ρ*Real.exp (u/2):ℝ):ℂ)

lemma wideGramLogKernel_smooth (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    ContDiff ℝ ∞ (wideGramLogKernel M hM W ρ) := by
  have he : (normProfileFourierSchwartz W hW hW' : ℂ → ℂ) = normProfileFourier W :=
    funext (normProfileFourierSchwartz_apply W hW hW')
  have hF : ContDiff ℝ ∞ (normProfileFourier W) := by
    rw [← he]
    exact (normProfileFourierSchwartz W hW hW').smooth ⊤
  apply (wideGramLogBump M hM).contDiff.smul
  exact hF.comp (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.div_const 2))))

def wideGramLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) : 𝓢(ℝ,ℂ) :=
  ((wideGramLogBump M hM).hasCompactSupport.smul_right (f' := fun u =>
    normProfileFourier W ((Real.sqrt ρ*Real.exp (u/2):ℝ):ℂ))).toSchwartzMap
      (wideGramLogKernel_smooth M hM W hW hW' ρ)

@[simp] lemma wideGramLogSchwartz_apply (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ u : ℝ) :
    wideGramLogSchwartz M hM W hW hW' ρ u = wideGramLogKernel M hM W ρ u := rfl

def wideGramMellinCoefficient (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ t : ℝ) : ℂ :=
  𝓕 (wideGramLogSchwartz M hM W hW hW' ρ) t

lemma wideGramMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (wideGramMellinCoefficient M hM W hW hW' ρ) :=
  (𝓕 (wideGramLogSchwartz M hM W hW hW' ρ)).integrable

lemma wideGramLogKernel_eq_radial (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    {ρ u : ℝ} (hρ : 0 ≤ ρ) (hu : |u| ≤ M) :
    wideGramLogKernel M hM W ρ u = radialDualProfile W (ρ*Real.exp u) := by
  have hcut : wideGramLogBump M hM u = 1 :=
    (wideGramLogBump M hM).one_of_mem_closedBall
      (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,wideGramLogBump] using hu)
  rw [wideGramLogKernel,hcut,one_smul,normProfileFourier_radial]
  congr 1
  rw [Complex.normSq_ofReal]
  calc
    _ = (Real.sqrt ρ*Real.sqrt ρ)*(Real.exp (u/2)*Real.exp (u/2)) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hρ,← Real.exp_add]; congr 2; ring

theorem wide_radial_mellin_separated (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ}
    (hρ : 0 ≤ ρ) (hx : 0 < x) (hy : 0 < y) (hxy : |Real.log x-Real.log y| ≤ M) :
    radialDualProfile W (ρ*x/y) = ∫ t : ℝ,
      wideGramMellinCoefficient M hM W hW hW' ρ t*gramMellinPhase t x*star (gramMellinPhase t y) := by
  have hk := wideGramLogKernel_eq_radial M hM W hρ hxy
  rw [Real.exp_sub,Real.exp_log hx,Real.exp_log hy,← mul_div_assoc] at hk
  rw [← hk]
  have he := congrArg (fun f : 𝓢(ℝ,ℂ) => f (Real.log x-Real.log y))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ,ℂ))
      (wideGramLogSchwartz M hM W hW hW' ρ))
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at he
  change wideGramLogSchwartz M hM W hW hW' ρ (Real.log x-Real.log y) = _
  rw [← he]
  apply integral_congr_ae
  filter_upwards with t
  have hi : inner ℝ t (Real.log x-Real.log y) = t*Real.log x-t*Real.log y := by
    simp only [RCLike.inner_apply,conj_trivial]
    ring
  have hp : (Real.fourierChar (inner ℝ t (Real.log x-Real.log y)):ℂ) =
      gramMellinPhase t x*star (gramMellinPhase t y) := by
    rw [hi,AddChar.map_sub_eq_div,div_eq_mul_inv,Circle.coe_mul,Circle.coe_inv_eq_conj]
    rfl
  change (Real.fourierChar (inner ℝ t (Real.log x-Real.log y)):ℂ)*
    wideGramMellinCoefficient M hM W hW hW' ρ t = _
  rw [hp]
  ring

end CubicFirstMoment

end

end OAI
