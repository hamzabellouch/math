import Mathlib
import OAI.Analysis.Conductivity.Geometry.TorusAffineField
import OAI.Analysis.Conductivity.Fourier.TorusSpectralContinuation

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

lemma torusRealContinuation_spectral_eventually {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) {x : Coord3} (hx : 0<x 0) :
    torusRealContinuation s (torusSpectralSynthesis s f)=ᶠ[𝓝 x]
      (fun y => (endFlatPoisson s f y).re) := by
  filter_upwards [(axial_halfspace_open 0).mem_nhds hx] with y hy
  rw [torusRealContinuation_spectral hs f hy,endFlatPoisson_eq]

lemma torusAffineField_spectral_covector {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) {x : Coord3} (hx : 0<x 0) :
    (fun k => fderiv ℝ (torusAffineField s κ (torusSpectralSynthesis s f)) x (Pi.single k 1))=
      fullEndFlatCovector s f κ (x 0) (torusAngles x) := by
  have he := torusRealContinuation_spectral_eventually hs f hx
  have hd := ((torusRealContinuation_smooth hs (torusSpectralSynthesis s f)).contDiffAt
    ((axial_halfspace_open 0).mem_nhds hx)).differentiableAt (by norm_num)
  have ha := ((hasFDerivAt_apply (𝕜:=ℝ) (0:Fin 3) x).const_mul κ)
  ext k
  change fderiv ℝ ((fun y : Coord3 => κ*y 0)+torusRealContinuation s (torusSpectralSynthesis s f)) x
    (Pi.single k 1)=(endPoissonField s f k.succ (x 0,torusAngles x)).re+κ*(Pi.single (0:Fin 3) (1:ℝ) : Coord3) k
  rw [(ha.add hd.hasFDerivAt).fderiv]
  change κ*(Pi.single k (1:ℝ) : Coord3) 0+fderiv ℝ (torusRealContinuation s (torusSpectralSynthesis s f)) x (Pi.single k 1)=_
  rw [he.fderiv_eq,endFlatPoisson_real_derivative_axis s hs f hx k]
  fin_cases k <;> simp
  ring

end ScalarConductivity

end
end

end OAI
