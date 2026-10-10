import Mathlib
import OAI.Computability.QuantumFactoring.FinalPolynomialResources
import OAI.Computability.QuantumFactoring.FinalUniformity

namespace OAI



section

/-! Complete source main theorem for the retained concrete physical family. -/
namespace ExactQuantumFactoring

/-- Source Theorem 1.1 (`thm:main`): exact factoring over the fixed gate set,
with a single finite-alphabet polynomial-time length-uniform generator and
polynomial worst-case gate and qubit counts. -/
theorem exact_quantum_factoring : MainTheorem := by
  exact ⟨PhysicalTree.finalCircuit, PhysicalTree.finalCircuit_uniform,
    PhysicalTree.finalCircuit_resources, PhysicalTree.finalCircuit_spec⟩

end ExactQuantumFactoring





end


end OAI
