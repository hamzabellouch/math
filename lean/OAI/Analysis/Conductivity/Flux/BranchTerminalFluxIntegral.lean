import Mathlib
import OAI.Analysis.Conductivity.Branching.BranchFiniteEnding
import OAI.Analysis.Conductivity.Fourier.SpectralAffineCovector
import OAI.Analysis.Conductivity.Fourier.SpectralTerminalIntegral

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal
local instance branchTerminalFluxIntegralMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance branchTerminalFluxIntegralProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torusAffineField_flux_normal {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) {R : ℝ} (hR : 0<R)
    (θ : UnitAddTorus (Fin 2)) :
    torusPeriodicDescent (flatModeFlux s (torusAffineField s κ (torusSpectralSynthesis s f))) (R,θ) 0=
      fullEndFlatCovector s f κ R θ 0 := by
  let x : Coord3 := ![R,2*Real.pi*torusRealRepresentative θ 0,2*Real.pi*torusRealRepresentative θ 1]
  have hx : 0<x 0 := hR
  change flatModeFlux s (torusAffineField s κ (torusSpectralSynthesis s f)) x 0=_
  rw [flatModeFlux_tensor,torusAffineField_spectral_covector hs f κ hx]
  have ha : torusAngles x=θ := (torusAngles_scaled R (torusRealRepresentative θ)).trans
    (torusRealProjection_representative θ)
  rw [ha]
  simp [flatBackgroundTensor,Matrix.mulVec,dotProduct,Fin.sum_univ_three,x]

lemma branchFluxCorrection_initial_integral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {f : Fin 2 → TorusL2} (i : Fin 3) (z : TorusEndingData s (branchNormalize i f))
    (j : Fin 2) (b : ℝ) (φ : Coord3 → ℝ) :
    (∫ θ,torusPeriodicDescent (branchFluxCorrection i z j) (0,θ) 0*φ (sourceAngularCollar b θ))=0 := by
  have he (θ : UnitAddTorus (Fin 2)) : torusPeriodicDescent (branchFluxCorrection i z j) (0,θ)=0 :=
    branchFluxCorrection_zero i z hs j _ rfl
  simp only [he,Pi.zero_apply,zero_mul,integral_zero]

lemma branchFluxCorrection_terminal_integral {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) {R : ℝ} (hR : 0<R) (hz : z.R<R) (b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ θ,torusPeriodicDescent (branchFluxCorrection i z j) (R,θ) 0*φ (sourceAngularCollar b θ))=
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s b hφ)-
        cylinderTerminalFlux s (centralBasisSlopes j i) R (f j) (smoothCollarTrace s b hφ) := by
  have he (θ : UnitAddTorus (Fin 2)) : torusPeriodicDescent (branchFluxCorrection i z j) (R,θ) 0=
      centralBasisSlopes j i-fullEndFlatCovector s (f j) (centralBasisSlopes j i) R θ 0 := by
    change branchFluxCorrection i z j ![R,2*Real.pi*torusRealRepresentative θ 0,
      2*Real.pi*torusRealRepresentative θ 1] 0=_
    rw [branchFluxCorrection_terminal i z j _ hz]
    change centralBasisSlopes j i*(Pi.single (0:Fin 3) (1:ℝ) : Coord3) 0-
      torusPeriodicDescent (flatModeFlux s (torusAffineField s (centralBasisSlopes j i)
        (torusSpectralSynthesis s (f j)))) (R,θ) 0=_
    rw [Pi.single_eq_same,mul_one,torusAffineField_flux_normal hs (f j) _ hR]
  simp_rw [he,sub_mul]
  have hq : Integrable (fun θ => φ (sourceAngularCollar b θ)) :=
    (hφ.continuous.comp (continuous_sourceAngularCollar b)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨hi,hI⟩ := fullEndFlatCovector_terminal_integral hs hR (f j) (centralBasisSlopes j i) b hφ
  rw [integral_sub (hq.const_mul _) hi,integral_const_mul,hI,smoothCollarTrace_mean_integral]

end ScalarConductivity

end
end

end OAI
