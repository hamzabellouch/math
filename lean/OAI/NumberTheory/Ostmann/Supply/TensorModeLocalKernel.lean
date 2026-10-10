import OAI.NumberTheory.Ostmann.Supply.LocalKernelPolynomial
import OAI.NumberTheory.Ostmann.Supply.TensorModePairing

namespace OAI

noncomputable section
namespace Ostmann.Supply.TensorModes
open TensorOperators

variable {p : ℕ} [NeZero p]

theorem centeredPart_scalarOnly (S T : Finset (ZMod p)) :
    (centeredPart (FiniteHilbertSpace.of (centeredSpace S))).comp (scalarOnly S T) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change centeredPart (FiniteHilbertSpace.of (centeredSpace S)) (scalarOnly S T x) = 0
  erw [centeredPart_apply]
  change WithLp.toLp 2 ((0 : ℂ), (0 : centeredSpace S)) = 0
  rfl

theorem scalarOnly_centeredPart (S T : Finset (ZMod p)) :
    (scalarOnly S T).comp (centeredPart (FiniteHilbertSpace.of (centeredSpace T))) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change scalarOnly S T (centeredPart (FiniteHilbertSpace.of (centeredSpace T)) x) = 0
  rw [centeredPart_apply]
  rfl

theorem localKernelPolynomial_zero_output (S : Finset (ZMod p)) (t : ℝ)
    (hS : S.Nonempty) (hT : Sᶜ.Nonempty) :
    (centeredPart (FiniteHilbertSpace.of (centeredSpace S))).comp
      (localKernelPolynomial S t (0,0)) = 0 := by
  rw [localKernelPolynomial_zero S t hS hT]
  exact centeredPart_scalarOnly S Sᶜ

theorem localKernelPolynomial_zero_input (S : Finset (ZMod p)) (t : ℝ)
    (hS : S.Nonempty) (hT : Sᶜ.Nonempty) :
    (localKernelPolynomial S t (0,0)).comp
      (centeredPart (FiniteHilbertSpace.of (centeredSpace Sᶜ))) = 0 := by
  rw [localKernelPolynomial_zero S t hS hT]
  exact scalarOnly_centeredPart S Sᶜ

end Ostmann.Supply.TensorModes

end

end OAI
