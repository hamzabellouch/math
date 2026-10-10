import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberTriangle
import OAI.Algebra.AuslanderReiten.Fibers.FiberFullHomCoordinates
import OAI.Algebra.AuslanderReiten.Homology.TriangleConnectingProduct

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)

theorem fiberSequenceFirst (n : ℤ) (v : FiberHom q H₁ H₂ n) :
    TriangleGradedSequence.first k (fiberEvaluationTriangle q H₁ H₂)
      (simpleHomotopyObject q) n v = fiberHomInclusion q H₁ H₂ n v := by
  erw [TriangleGradedSequence.first_eq_shift, fiberEvaluationTriangle_first]
  rfl

theorem fiberRhoPair_eq_first (n : ℤ) (v : FiberHom q H₁ H₂ n) :
    fiberHomRhoPair q H₁ H₂ n v = middleHomEquiv q H₁ H₂ n
      (TriangleGradedSequence.first k (fiberEvaluationTriangle q H₁ H₂)
        (simpleHomotopyObject q) n v) := by
  rw [fiberSequenceFirst]
  exact (middleHomEquiv_inclusion q H₁ H₂ n v).symm

theorem fiberRhoPair_bijective_of_first (n : ℤ)
    (hf : Function.Bijective (TriangleGradedSequence.first k
      (fiberEvaluationTriangle q H₁ H₂) (simpleHomotopyObject q) n)) :
    Function.Bijective (fiberHomRhoPair q H₁ H₂ n) := by
  have hmap : (fiberHomRhoPair q H₁ H₂ n : FiberHom q H₁ H₂ n → _) =
      (middleHomEquiv q H₁ H₂ n) ∘
        (TriangleGradedSequence.first k (fiberEvaluationTriangle q H₁ H₂)
          (simpleHomotopyObject q) n) := funext (fiberRhoPair_eq_first q H₁ H₂ n)
  rw [hmap]
  exact (middleHomEquiv q H₁ H₂ n).bijective.comp hf

theorem fiberFullRhoPair_bijective_of_rho (n : ℤ)
    (hf : Function.Bijective (fiberHomRhoPair q H₁ H₂ n)) :
    Function.Bijective (fiberFullRhoPair q H₁ H₂ n) :=
  ((simpleFullHomEquiv q n).symm.prodCongr (simpleFullHomEquiv q n).symm).bijective.comp
    (hf.comp (fiberFullHomEquiv q H₁ H₂ n).bijective)

end ArExplicit.T

end

end OAI
