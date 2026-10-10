import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondClassicalFlux

namespace OAI

/-! Recover a classical scalar channel on any positive annulus from a flux primitive. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLocalFlux_classical (ell : ℕ) (R l r : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hr : r ≤ R) (w a : SpectralHarmonicWeight R)
    (u : SpectralHarmonicPair ell R) (P G : ℝ → ℂ)
    (hw : ContinuousOn w.density (Ioo l r)) (ha : ContinuousOn a.density (Ioo l r))
    (hpos : ∀ x ∈ Ioo l r, 0 < w.density x)
    (hP : ∀ x ∈ Ioo l r, HasDerivAt P (G x) x)
    (hflux : ∀ᵐ x, x ∈ Ioo l r → spectralSecondFlux ell R w a u x=P x) :
    (∀ x ∈ Ioo l r, DifferentiableAt ℝ (spectralHarmonicRepresentative ell R hR u.snd) x) ∧
      ContinuousOn (deriv (spectralHarmonicRepresentative ell R hR u.snd)) (Ioo l r) ∧
      ∀ x ∈ Ioo l r, HasDerivAt (spectralSecondClassicalFlux ell R hR w a u) (G x) x := by
  have hPc : ContinuousOn P (Ioo l r) := fun x hx => (hP x hx).continuousAt.continuousWithinAt
  have hd (x : ℝ) (hx : x ∈ Ioo l r) :=
    spectralSecondFlux_hasDerivAt ell R l r hR hl hr w a u P hw ha hpos hPc hflux x hx
  have hDc := spectralSecondDerivativeValue_continuousOn ell R l r hR hl hr w a u P hw ha hpos hPc
  refine ⟨fun x hx => (hd x hx).differentiableAt,hDc.congr (fun x hx => (hd x hx).deriv),?_⟩
  intro x hx
  apply (hP x hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact spectralSecondClassicalFlux_eq ell R hR w a u P y (hl.trans hy.1).ne'
    (hpos y hy).ne' (hd y hy)

end DefocusingNLS

end OAI
