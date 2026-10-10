import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlowSmooth
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormedLiePolynomial

namespace OAI

/-! # Composing the polynomial operations used in a nilpotent extension -/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {L V : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {r : ℕ∞ω}

theorem contDiff_derivationFlow_comp
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
    {f : V → ℝ} {g : V → L} (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    ContDiff ℝ r (fun x => nilpotentDerivationFlow D hD (f x) (g x)) := by
  have hp : ContDiff ℝ r (fun x : V => (f x, g x)) := hf.prodMk hg
  have h := ContDiff.comp
    (f := fun x : V => (f x, g x))
    (g := fun p : ℝ × L => nilpotentDerivationFlow D hD p.1 p.2)
    (contDiff_nilpotentDerivationFlow D hD (r := r)) hp
  exact h

theorem contDiff_binaryDynkin_comp {c : ℕ} (coeff : DynkinCoefficients c 2)
    {f g : V → L} (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    ContDiff ℝ r (fun x => finiteDynkinPolynomial coeff ![f x, g x]) := by
  apply contDiff_normed_finiteDynkinPolynomial
  intro i
  fin_cases i
  · exact hf
  · exact hg

end PolycyclicRecognition

end

end OAI
