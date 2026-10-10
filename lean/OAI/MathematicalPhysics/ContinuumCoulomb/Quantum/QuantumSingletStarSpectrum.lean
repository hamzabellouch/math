import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSingletStarBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingSpectrum

namespace OAI

/-! Ground-energy estimate for the finite singlet stars used in routing. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {κ : Type*} [Fintype κ]

theorem qmaSingletStar_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (e : Fin r) (site : κ → Fin n) (member : κ → Fin 2) (amplitude : κ → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ a, |amplitude a| ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (routingHamiltonian n r Delta C
        (qmaSingletStar n r e site member amplitude)) -
      sourceMatrixBottom n (C - mediatorCompression n r
        (qmaSingletStar n r e site member amplitude * liftedMediatorInverse n r Delta *
          qmaSingletStar n r e site member amplitude))| ≤ 16 * Delta * epsilon ^ 3 := by
  have hb : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      ‖spinMatrixOperator (qmaSingletStar n r e site member amplitude)‖ ≤ epsilon * (4 * Delta) :=
    calc
      _ ≤ ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
          3*∑ a, |amplitude a| := add_le_add le_rfl (qmaSingletStar_norm n r e site member amplitude)
      _ ≤ epsilon * (4 * Delta) := hbound
  exact routing_bottom n r hDelta C hC (qmaSingletStar n r e site member amplitude)
    (qmaSingletStar_star n r e site member amplitude)
    (qmaSingletStar_low n r e site member amplitude) hepsilon hsmall hb

theorem qmaRoutingStars_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |amplitude e a| ≤ epsilon * (4*Delta)) :
    |mediatorFullBottom n r (routingHamiltonian n r Delta C
        (qmaRoutingStars n r site member amplitude)) -
      sourceMatrixBottom n (C - mediatorCompression n r
        (qmaRoutingStars n r site member amplitude * liftedMediatorInverse n r Delta *
          qmaRoutingStars n r site member amplitude))| ≤ 16*Delta*epsilon^3 := by
  have hb : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      ‖spinMatrixOperator (qmaRoutingStars n r site member amplitude)‖ ≤ epsilon * (4*Delta) := by
    calc
      _ ≤ ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
          3*∑ e, ∑ a, |amplitude e a| := add_le_add le_rfl (qmaRoutingStars_norm n r site member amplitude)
      _ ≤ epsilon * (4*Delta) := hbound
  exact routing_bottom n r hDelta C hC (qmaRoutingStars n r site member amplitude)
    (qmaRoutingStars_star n r site member amplitude)
    (qmaRoutingStars_low n r site member amplitude) hepsilon hsmall hb

end ContinuumCoulomb

end

end OAI
