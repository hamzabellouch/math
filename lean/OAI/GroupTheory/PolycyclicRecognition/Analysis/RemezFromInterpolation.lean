import OAI.GroupTheory.PolycyclicRecognition.Analysis.RemezInput
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateRemez

namespace OAI

/-! # Polynomial mass estimates from interpolation

Separated interpolation points and finite-measure Fubini give the
scalar sublevel estimate with exponent the dimension times the degree.
-/

noncomputable section
namespace PolycyclicRecognition

theorem remezPolynomialInput : RemezPolynomialInput := by
  intro n D _ hD
  obtain ⟨A, hA, hbound⟩ := coordinate_polynomial_remez n D hD
  refine ⟨A, hA, ?_⟩
  intro p hp R hR S hS hSR hm η hη hv x hx
  exact hbound (fun y => MvPolynomial.eval y p) (coordinatePolynomial_eval p hp)
    R hR S hS hSR hm η hη hv x hx

end PolycyclicRecognition

end

end OAI
