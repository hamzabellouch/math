import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CentralTransgressionHomologyExact
import Mathlib.RingTheory.Flat.TorsionFree

namespace OAI

/-! # The central-extension comparison after rationalization

Flatness of the rationals preserves both exact pairs of the integral
comparison. The source remains explicitly the rationalization of actual
integral group homology.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {N G Q : Type} [CommGroup N] [Group G] [Group Q]
variable (E : GroupExtension N G Q) (hc : E.inl.range ≤ Subgroup.center G)

def rationalCentralTransgression (σ : E.Section) :
    (ℚ ⊗[ℤ] groupHomology.H2 (integralTrivialCoefficient Q)) →ₗ[ℚ] (ℚ ⊗[ℤ] Additive N) :=
  (centralExtensionTransgression E hc σ).baseChange ℚ

theorem rationalCentralTransgression_exact_H2 (σ : E.Section) :
    Function.Exact
      ((groupHomology.map E.rightHom (groupIntegralTrivialCoefficientMap E.rightHom) 2).hom.baseChange ℚ)
      (rationalCentralTransgression E hc σ) := by
  have hi := (LinearMap.exact_iff).mpr
    (centralExtensionTransgression_exact_H2 E hc σ).symm
  have he := Module.Flat.lTensor_exact ℚ hi
  simpa only [rationalCentralTransgression, LinearMap.baseChange_eq_ltensor] using he

theorem rationalCentralTransgression_exact_kernel (σ : E.Section) :
    Function.Exact (rationalCentralTransgression E hc σ)
      ((centralExtensionAbelianizationMap E).baseChange ℚ) := by
  have hi := (LinearMap.exact_iff).mpr (centralExtensionTransgression_range E hc σ).symm
  have he := Module.Flat.lTensor_exact ℚ hi
  simpa only [rationalCentralTransgression, LinearMap.baseChange_eq_ltensor] using he

end PolycyclicRecognition

end

end OAI
