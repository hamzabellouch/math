import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFrameValue

namespace OAI

/-! The coefficient selected by the terminal first coordinate stays away
from zero under a bounded oscillatory action. -/

open Set
namespace DefocusingNLS

theorem spectralWKB_branch_amplitude
    (R E B kR kE : ℝ) (hRE : R ≤ E) (chi : ℂ) (hchi : ‖chi‖ = 1)
    (p v : ℝ → ℂ) (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hp0 : ∀ t ∈ Icc R E, p t ≠ 0)
    (hpD : ∀ t ∈ Ioo R E, HasDerivAt p (v t) t)
    (hkR : 0 < kR) (hkE : 0 < kE) (hkRp : kR^2 = ‖p R‖) (hkEp : kE^2 = ‖p E‖)
    (hsmall : ‖v R‖ ≤ ‖p R‖^2)
    (hphase : |(spectralWKBPhase R chi p E).re| ≤ B)
    (x : ℂ) (hxlo : 1 ≤ kE*‖x‖) (hxhi : kE*‖x‖ ≤ 2) :
    let z := x/(spectralWKBFrame R chi p v E).1
    Real.exp (-B) ≤ ‖z‖ ∧ ‖z‖ ≤ 2*Real.exp B ∧
      spectralShellNorm kR (z • spectralWKBFrame R chi p v R) ≤ 5*Real.exp B := by
  dsimp only
  have hvE := spectralWKBFrame_value_norm R E hRE chi p v hp hv hp0 hpD kE E hkE hkEp ⟨hRE,le_rfl⟩
  obtain ⟨hzlo,hzhi⟩ := spectralFrame_amplitude_bounds kE (spectralWKBPhase R chi p E).re B x
    (spectralWKBFrame R chi p v E).1 hkE hvE hphase hxlo hxhi
  refine ⟨hzlo,hzhi,?_⟩
  have hDr : spectralShellNorm kR (spectralWKBFrame R chi p v R) ≤ 5/2 := by
    rw [spectralWKBFrame_initial]
    simpa only [Complex.zero_re,Real.exp_zero,mul_one] using
      spectralWKBState_shell_bound chi (p R) (v R) (spectralWKBInitialAmplitude (p R)) 0
        kR hkR hkRp (spectralWKBInitialAmplitude_normalization (p R) (hp0 R ⟨le_rfl,hRE⟩))
        hchi.le hsmall
  rw [spectralShellNorm_smul]
  calc
    _ ≤ (2*Real.exp B)*(5/2) := mul_le_mul hzhi hDr
      (spectralShellNorm_nonneg kR hkR.le _) (by positivity)
    _ = _ := by ring

end DefocusingNLS

end OAI
