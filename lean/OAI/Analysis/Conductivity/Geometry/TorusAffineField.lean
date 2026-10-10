import Mathlib
import OAI.Analysis.Conductivity.Fourier.AffineFourierField
import OAI.Analysis.Conductivity.Flux.FlatBackgroundTensor
import OAI.Analysis.Conductivity.Fourier.TorusLeadingRealMode
import OAI.Analysis.Conductivity.Fourier.TorusSmoothModeJet

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

def torusAffineField (s : Fin 3 → ℝ) (κ : ℝ) (f : TorusL2) (x : Coord3) : ℝ :=
  κ*x 0+torusRealContinuation s f x

lemma torusAffineField_smooth {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (κ : ℝ) (f : TorusL2) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (torusAffineField s κ f) {x | 0<x 0} :=
  (show ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => κ*x 0) by fun_prop).contDiffOn.add
    (torusRealContinuation_smooth hs f)

lemma torusAffineField_periodic (s : Fin 3 → ℝ) (κ : ℝ) (f : TorusL2) :
    AngularPeriodic (2*Real.pi) (torusAffineField s κ f) := by
  intro n x
  simp only [torusAffineField,torusRealContinuation,torusAngles_shift]
  simp [angularShift]

lemma torusAffineField_polar_eventually {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (κ : ℝ) (f : TorusL2) {x : Coord3} (hx : 0<x 0) :
    torusAffineField s κ f=ᶠ[𝓝 x]
      affineFourierField s (realTorusAmplitude f) (realTorusPhase f) κ (mFourierCoeff f 0).re := by
  filter_upwards [(axial_halfspace_open 0).mem_nhds hx] with y hy
  simp only [torusAffineField,affineFourierField,torusRealContinuation_mean_free hs f hy]
  ring

lemma torusAffineField_flux_divergence {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (κ : ℝ) (f : TorusL2) {x : Coord3} (hx : 0<x 0) :
    coordinateDivergence (flatModeFlux s (torusAffineField s κ f)) x=0 := by
  have he := torusAffineField_polar_eventually hs κ f hx
  have hf : flatModeFlux s (torusAffineField s κ f)=ᶠ[𝓝 x]
      flatModeFlux s (affineFourierField s (realTorusAmplitude f) (realTorusPhase f) κ (mFourierCoeff f 0).re) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
    simp only [flatModeFlux,hy]
  rw [coordinateDivergence_congr_nhds hf,flatModeFlux_divergence
    ((affineFourierField_smooth hs (realTorusAmplitude_bound f) κ (mFourierCoeff f 0).re).contDiffAt
      ((axial_halfspace_open 0).mem_nhds hx)),
    affineFourierField_harmonic hs (realTorusAmplitude_bound f) κ (mFourierCoeff f 0).re hx]

lemma flatModeFlux_tensor (s : Fin 3 → ℝ) (f : Coord3 → ℝ) (x : Coord3) :
    flatModeFlux s f x=flatBackgroundTensor s*ᵥ(fun i => fderiv ℝ f x (Pi.single i 1)) := by
  ext i
  fin_cases i <;> simp [flatModeFlux,flatBackgroundTensor,Matrix.mulVec,dotProduct,Fin.sum_univ_three,flatAxis]

end ScalarConductivity

end
end

end OAI
