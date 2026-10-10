import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarRobinError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGreenBranchBounds

namespace OAI

/-! The full Green bound controls both the coupled forcing and a remote
Robin derivative error relative to the prescribed inner value. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_full_boundary_error
    (R E r kap A C B M : ℝ) (hR : 0 < R) (hr : r ∈ Icc R E)
    (hkap : 0 < kap) (hA : 0 ≤ A) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (k : ℝ → ℝ) (hk : ∀ t ∈ Icc R E, kap ≤ k t)
    (D U q : ℝ → ℂ × ℂ) (V f : ℝ → ℂ) (W beta : ℂ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hfc : ContinuousOn f (Icc R E))
    (hW : W ≠ 0) (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t) = W)
    (hD : ∀ t ∈ Icc R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Icc R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Icc R E, HasDerivAt q (spectralScalarField (V t) (q t)+(0,f t)) t)
    (hDR : (D R).1 = 0) (hUR : (U R).1 ≠ 0) (hUE : (U E).2 = beta*(U E).1)
    (hgreen : ∀ t ∈ Icc R E, spectralShellNorm (k r) (spectralScalarGreenState D U W r t) ≤ A/(k t))
    (hforcing : ∀ t ∈ Icc R E, ‖f t‖ ≤ C/(kap*t^2)*M)
    (hboundary : ‖(q E).2-beta*(q E).1‖ ≤ B/kap*M) :
    spectralShellNorm (k r) (q r-((q R).1/(U R).1) • U r) ≤
      ((A+1)*(B+C/R)/kap^2)*M := by
  obtain ⟨hl,hrt⟩ := spectralGreen_closed_branch_bounds D U W k R E A kap r
    hr hA hkap hk hW (hdet r hr) hgreen
  have hb := spectralScalar_outgoing_extension_error R E r (k r) kap (A+1) C M (B/kap*M)
    hR hr (hkap.trans_le (hk r hr)).le hkap (by linarith) hC hM D U q V f W beta
    hDc hUc hqc hfc hW hdet hD hU hq hDR hUR hUE hl hrt hforcing hboundary
  apply hb.trans_eq
  field_simp

end DefocusingNLS

end OAI
