import OAI.Probability.SLE.Gauge.SerpentineCompleteEmbedding
import OAI.Probability.SLE.LoewnerReflection

namespace OAI

/-! Reflecting the deterministic ribbon to the left of the imaginary
axis preserves its chart geometry. No stochastic symmetry is used. -/

noncomputable section
open Set Metric ComplexConjugate
open scoped NNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

def reflectedChart (P : ℂ → ℂ) (z : ℂ) : ℂ := loewnerMirror (P (conj z))

lemma conj_mem_closedRibbon {z : ℂ} (hz : z ∈ closedRibbon) : conj z ∈ closedRibbon := by
  simpa only [closedRibbon, mem_ofPred_eq, Complex.conj_re, Complex.conj_im, abs_neg] using hz

lemma conj_mem_stepPatch {k : ℝ} {z : ℂ} (hz : z ∈ ribbonStepPatch k) :
    conj z ∈ ribbonStepPatch k := by
  simpa only [ribbonStepPatch, mem_ofPred_eq, Complex.conj_re, Complex.conj_im, abs_neg] using hz

lemma reflectedChart_continuous {P : ℂ → ℂ} (hP : Continuous P) : Continuous (reflectedChart P) :=
  loewnerMirror.continuous.comp (hP.comp Complex.continuous_conj)

lemma reflectedChart_injective {P : ℂ → ℂ} (hP : InjOn P closedRibbon) :
    InjOn (reflectedChart P) closedRibbon := by
  intro z hz w hw he
  have hh := hP (conj_mem_closedRibbon hz) (conj_mem_closedRibbon hw) (loewnerMirror.injective he)
  exact Complex.conjLIE.injective hh

lemma reflectedChart_patch_upper {P : ℂ → ℂ} {C : ℝ≥0} {k : ℝ}
    (hP : LipschitzOnWith C P (ribbonStepPatch k)) :
    LipschitzOnWith C (reflectedChart P) (ribbonStepPatch k) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro z hz w hw
  simpa only [reflectedChart, loewnerMirror_dist, Complex.dist_conj_conj] using
    hP.dist_le_mul _ (conj_mem_stepPatch hz) _ (conj_mem_stepPatch hw)

lemma reflectedChart_patch_lower {P : ℂ → ℂ} {L k : ℝ}
    (hP : ∀ z ∈ ribbonStepPatch k, ∀ w ∈ ribbonStepPatch k, dist z w ≤ L * dist (P z) (P w)) :
    ∀ z ∈ ribbonStepPatch k, ∀ w ∈ ribbonStepPatch k,
      dist z w ≤ L * dist (reflectedChart P z) (reflectedChart P w) := by
  intro z hz w hw
  simpa only [reflectedChart, loewnerMirror_dist, Complex.dist_conj_conj] using
    hP (conj z) (conj_mem_stepPatch hz) (conj w) (conj_mem_stepPatch hw)

lemma reflectedChart_upper {P : ℂ → ℂ}
    (hP : ∀ z ∈ closedRibbon, 0 < z.re → P z ∈ upperHalfPlane) :
    ∀ z ∈ closedRibbon, 0 < z.re → reflectedChart P z ∈ upperHalfPlane := by
  intro z hz hz0
  have hh := hP (conj z) (conj_mem_closedRibbon hz) (by simpa using hz0)
  simpa only [reflectedChart, upperHalfPlane, mem_ofPred_eq, loewnerMirror_im] using hh

lemma reflectedChart_initial {P : ℂ → ℂ} {H : ℝ}
    (hP : ∀ z ∈ closedRibbon, z.re ≤ H → P z = Complex.I * z) :
    ∀ z ∈ closedRibbon, z.re ≤ H → reflectedChart P z = Complex.I * z := by
  intro z hz hzH
  rw [reflectedChart, hP (conj z) (conj_mem_closedRibbon hz) (by simpa using hzH)]
  simp [loewnerMirror]

lemma reflectedChart_width {P : ℂ → ℂ} {σ : ℝ → ℂ}
    (hwidth : ∀ z ∈ closedRibbon, ‖P z - σ z.re‖ ≤ 1) :
    ∀ z ∈ closedRibbon, ‖reflectedChart P z - loewnerMirror (σ z.re)‖ ≤ 1 := by
  intro z hz
  have hh := hwidth (conj z) (conj_mem_closedRibbon hz)
  rw [← dist_eq_norm, reflectedChart, loewnerMirror_dist]
  simpa only [dist_eq_norm, Complex.conj_re] using hh

end SLEExactGauge.Serpentine

end

end OAI
