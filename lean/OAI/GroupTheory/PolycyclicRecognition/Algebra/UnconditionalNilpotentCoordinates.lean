import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialIdealExtensionCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AbelianLieModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianDynkinInput

namespace OAI

/-! # Polynomial nilpotent models by dimension induction

At each successor step, the ideal already has polynomial coordinates. A
faithful representation of its semidirect extension proves that extension's
finite product law, from which its own exponential coordinates are constructed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

theorem polynomialExponentialCoordinates_nilpotent
    (L : Type) [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
    (hnil : LieRing.IsNilpotent L) : Nonempty (PolynomialExponentialCoordinates L) := by
  have hmain : ∀ n : ℕ, ∀ (A : Type) [RealNormedLieAlgebra A] [FiniteDimensional ℝ A],
      finrank ℝ A = n → LieRing.IsNilpotent A → Nonempty (PolynomialExponentialCoordinates A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ _ hdim hA
      let : LieRing.IsNilpotent A := hA
      by_cases hs : Subsingleton A
      · let := hs
        let N := abelianLieModel (V := A)
        let _ : CommGroup N.carrier := inferInstanceAs (CommGroup (Multiplicative A))
        exact polynomialExponentialCoordinates_of_model N hA
          (nilpotentDynkinExpansionInput_of_comm (E := N.modelSpace) (G := N.carrier))
      · let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hs
        obtain ⟨C⟩ := exists_nilpotentCodimensionOneData (L := A)
        let := C.normedIdeal
        have hsmaller : finrank ℝ C.ideal < n := by
          rw [← hdim]
          exact C.finrank_ideal_lt
        obtain ⟨P⟩ := ih (finrank ℝ C.ideal) hsmaller C.ideal rfl C.ideal_nilpotent
        exact polynomialCoordinates_extend_ideal C P
  exact hmain (finrank ℝ L) L rfl hnil

end PolycyclicRecognition

end

end OAI
