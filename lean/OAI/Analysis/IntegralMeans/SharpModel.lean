import OAI.Analysis.IntegralMeans.Model
import OAI.Analysis.IntegralMeans.Koebe

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Brennan.Sharp

def koebeDomain : Set ℂ := koebeMap '' disk

def koebeInverse : ℂ → ℂ := Function.invFunOn koebeMap disk

def areaMoment (f : ℂ → ℂ) (U : Set ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ t) ∂volume

def SharpEndpointStatement : Prop :=
  Schlicht koebeMap ∧
  areaMoment koebeMap disk (-2) = ⊤ ∧
  areaMoment koebeMap disk (2 / 3) = ⊤ ∧
  ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 : ℝ)) koebeDomain volume ∧
  ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 / 3 : ℝ)) koebeDomain volume

end Brennan.Sharp

end

end OAI
