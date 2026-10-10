import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleActionOrder

namespace OAI

/-! Endpoint bounds control the reflected WKB error uniformly when the
left endpoint moves through a fixed shell. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralLiouvilleConeError (h b eta omega gamma R E : ℝ) : ℝ :=
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
  let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
  let H := (∫ t in R..E, p t).re
  (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H)

theorem spectralLiouvilleConeError_uniform (h b eta omega gamma R B E eps : ℝ)
    (hR : 0 < R) (hRB : R ≤ B) (hBE : B ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hlo : spectralLiouvilleConeError h b eta omega gamma R E ≤ eps)
    (hhi : spectralLiouvilleConeError h b eta omega gamma B E ≤ eps) :
    ∀ r ∈ Icc R B, spectralLiouvilleConeError h b eta omega gamma r E ≤ 2*eps := by
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
  let j := fun t => (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
  let J := fun r => ∫ t in r..E, j t
  let H := fun r => (∫ t in r..E, p t).re
  have hRE := hRB.trans hBE
  have hjc : ContinuousOn j (Icc R E) := by
    have hc := (spectralLiouvilleResidual_continuousOn (-1) h b eta omega gamma R E
      (by norm_num) hR hF).2.const_mul (25/4 : ℝ)
    convert hc using 1
    funext t
    dsimp only [j,p]
    ring
  have hj0 : ∀ t, 0 ≤ j t := fun _ => by dsimp only [j]; positivity
  have hJn (r : ℝ) (hr : r ∈ Icc R E) : 0 ≤ J r :=
    intervalIntegral.integral_nonneg_of_forall hr.2 hj0
  have hJa (r : ℝ) (hr : r ∈ Icc R E) : J r ≤ J R :=
    intervalIntegral.integral_mono_interval hr.1 hr.2 le_rfl
      (Filter.Eventually.of_forall hj0) (hjc.intervalIntegrable_of_Icc hRE)
  have hHa : AntitoneOn H (Icc R E) := spectralLiouville_action_antitone h b eta omega gamma R E hR hF
  change (25/4 : ℝ)*Real.exp (J R)*J R+(25/8)*Real.exp (-2*H R) ≤ eps at hlo
  change (25/4 : ℝ)*Real.exp (J B)*J B+(25/8)*Real.exp (-2*H B) ≤ eps at hhi
  have hlow : (25/4 : ℝ)*Real.exp (J R)*J R ≤ eps := by
    have hp : 0 ≤ (25/8 : ℝ)*Real.exp (-2*H R) := by positivity
    linarith
  have hhigh : (25/8 : ℝ)*Real.exp (-2*H B) ≤ eps := by
    have hp : 0 ≤ (25/4 : ℝ)*Real.exp (J B)*J B :=
      mul_nonneg (by positivity) (hJn B ⟨hRB,hBE⟩)
    linarith
  intro r hr
  have hrE : r ∈ Icc R E := ⟨hr.1,hr.2.trans hBE⟩
  have hJ := hJa r hrE
  have hH := hHa hrE ⟨hRB,hBE⟩ hr.2
  have hterm1 : (25/4 : ℝ)*Real.exp (J r)*J r ≤ (25/4 : ℝ)*Real.exp (J R)*J R := by
    have hJr := hJn r hrE
    gcongr
  have hterm2 : (25/8 : ℝ)*Real.exp (-2*H r) ≤ (25/8 : ℝ)*Real.exp (-2*H B) := by
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  change (25/4 : ℝ)*Real.exp (J r)*J r+(25/8)*Real.exp (-2*H r) ≤ 2*eps
  linarith

end DefocusingNLS

end OAI
