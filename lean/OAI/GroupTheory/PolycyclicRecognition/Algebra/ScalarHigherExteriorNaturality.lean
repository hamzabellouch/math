import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ScalarHigherHomologyExterior
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianMultilinearNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ExteriorSquareHomologyNaturality

namespace OAI

/-! # Naturality of the higher homology-to-exterior map -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K : Type) [Field K] {A B : Type} [CommGroup A] [CommGroup B]

theorem scalarIntegralExterior_natural (f : A →* B) (n : ℕ) (v : Fin n → A) :
    exteriorPower.map n ((additiveGroupLinearMap f).baseChange K)
        (scalarIntegralExterior K A n (Additive.ofMul ∘ v)) =
      scalarIntegralExterior K B n (Additive.ofMul ∘ (f ∘ v)) := by
  rw [scalarIntegralExterior_apply, scalarIntegralExterior_apply,
    exteriorPower.map_apply_ιMulti]
  congr 1

theorem scalarIntegralHomology_natural (f : A →* B) (n : ℕ)
    (z : groupHomology (integralTrivialCoefficient A) n) :
    abelianMultilinearHomology (scalarIntegralExterior K B n).toMultilinearMap
        (groupHomology.map f (integralTrivialCoefficientMap f) n z) =
      exteriorPower.map n ((additiveGroupLinearMap f).baseChange K)
        (abelianMultilinearHomology (scalarIntegralExterior K A n).toMultilinearMap z) :=
  abelianMultilinearHomology_natural f _ _
    ((exteriorPower.map n ((additiveGroupLinearMap f).baseChange K)).restrictScalars ℤ)
    (scalarIntegralExterior_natural K f n) z

theorem scalarHomologyExterior_natural (f : A →* B) (n : ℕ) :
    (scalarHomologyExterior K B n).comp
        ((groupHomology.map f (integralTrivialCoefficientMap f) n).hom.baseChange K) =
      (exteriorPower.map n ((additiveGroupLinearMap f).baseChange K)).comp
        (scalarHomologyExterior K A n) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro r z
  change r • abelianMultilinearHomology (scalarIntegralExterior K B n).toMultilinearMap
      (groupHomology.map f (integralTrivialCoefficientMap f) n z) =
    exteriorPower.map n ((additiveGroupLinearMap f).baseChange K)
      (r • abelianMultilinearHomology (scalarIntegralExterior K A n).toMultilinearMap z)
  rw [map_smul, scalarIntegralHomology_natural]

end PolycyclicRecognition

end

end OAI
