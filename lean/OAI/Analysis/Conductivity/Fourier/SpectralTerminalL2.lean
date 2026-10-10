import Mathlib
import OAI.Analysis.Conductivity.Flux.CylinderSlopeGreen

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sqrt_rate_exp_bound {r R : ℝ} (hr : 0≤r) (hR : 0<R) :
    |Real.sqrt r*Real.exp (-r*R)|≤1+R⁻¹ := by
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)]
  have hs : Real.sqrt r≤1+r := by
    have := Real.sq_sqrt hr
    nlinarith [Real.sqrt_nonneg r,sq_nonneg r]
  have he : Real.exp (-r*R)≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hm : r*R≤Real.exp (r*R) := le_trans (by linarith) (Real.add_one_le_exp (r*R))
  have hexp : Real.exp (r*R)*Real.exp (-r*R)=1 := by rw [←Real.exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-r*R)).le
  rw [hexp] at hmul
  have hi : R*R⁻¹=1 := mul_inv_cancel₀ hR.ne'
  have hb : r*Real.exp (-r*R)≤R⁻¹ := by nlinarith
  have ht := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-r*R)).le
  nlinarith

def spectralTerminalDensity (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (f : spectralTraceGraph (torusRate s)) : SpectralL2 TorusModes :=
  sequenceMultiplier (fun h => ((Real.sqrt (torusRate s h)*Real.exp (-torusRate s h*R):ℝ):ℂ))
    (1+R⁻¹) (by positivity)
    (fun h => by simpa only [Complex.norm_real,Real.norm_eq_abs] using
      sqrt_rate_exp_bound (r:=torusRate s h) (Real.sqrt_nonneg _) hR) (f.val 1)

lemma spectralTerminalDensity_pair (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (f g : spectralTraceGraph (torusRate s)) :
    inner ℂ (spectralTerminalDensity s hR f) (g.val 0)=
      spectralWeightedPairL s (spectralEndWeight s R f) g := by
  change inner ℂ (spectralTerminalDensity s hR f) (g.val 0)=
    inner ℂ (spectralEndWeight s R f) (g.val 1)
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro h
  change inner ℂ (((Real.sqrt (torusRate s h)*Real.exp (-torusRate s h*R):ℝ):ℂ)*f.val 1 h)
    (g.val 0 h)=inner ℂ ((Real.exp (-torusRate s h*|R|):ℂ)*f.val 1 h) (g.val 1 h)
  rw [g.property h,abs_of_pos hR]
  simp only [RCLike.inner_apply,map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
  ring

def terminalFluxL2CLM (s : Fin 3 → ℝ) (κ : ℝ) {R : ℝ} (hR : 0<R)
    (f : spectralTraceGraph (torusRate s)) : SpectralL2 TorusModes →L[ℝ] ℝ :=
  κ • Complex.reCLM.comp ((lp.evalCLM ℂ (fun _ : TorusModes => ℂ) 2 0).restrictScalars ℝ)-
    Complex.reCLM.comp ((innerSL ℂ (spectralTerminalDensity s hR f)).restrictScalars ℝ)

lemma terminalFluxL2CLM_trace (s : Fin 3 → ℝ) (κ : ℝ) {R : ℝ} (hR : 0<R)
    (f g : spectralTraceGraph (torusRate s)) :
    terminalFluxL2CLM s κ hR f (g.val 0)=cylinderTerminalFlux s κ R f g := by
  change κ*(g.val 0 0).re-(inner ℂ (spectralTerminalDensity s hR f) (g.val 0)).re=_
  rw [spectralTerminalDensity_pair]
  rfl

end ScalarConductivity

end
end

end OAI
