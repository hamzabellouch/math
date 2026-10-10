import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentCodimensionOneModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AbelianLieModel

namespace OAI

/-! # Nilpotent model existence by dimension induction

Only the published finite BCH formula on already constructed, smaller models
is used. No general Lie existence or integration theorem is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable (dynkin : ∀ (K : Type) [LieRing K] [LieAlgebra ℝ K] [FiniteDimensional ℝ K]
  (N : NilpotentLieModel K), NilpotentDynkinExpansionInput N.modelSpace N.carrier)

include dynkin

theorem nilpotentLieModel_of_dynkin
    (L : Type) [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
    (hnil : LieRing.IsNilpotent L) : Nonempty (NilpotentLieModel L) := by
  have hmain : ∀ n : ℕ, ∀ (A : Type) [RealNormedLieAlgebra A] [FiniteDimensional ℝ A],
      finrank ℝ A = n → LieRing.IsNilpotent A → Nonempty (NilpotentLieModel A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ _ hdim hA
      let : LieRing.IsNilpotent A := hA
      by_cases hs : Subsingleton A
      · let := hs
        exact ⟨abelianLieModel (V := A)⟩
      · let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hs
        obtain ⟨C⟩ := exists_nilpotentCodimensionOneData (L := A)
        let := C.normedIdeal
        have hsmaller : finrank ℝ C.ideal < n := by
          rw [← hdim]
          exact C.finrank_ideal_lt
        have hI : LieRing.IsNilpotent C.ideal := C.ideal_nilpotent
        obtain ⟨N⟩ := ih (finrank ℝ C.ideal) hsmaller C.ideal rfl hI
        obtain ⟨P⟩ := polynomialExponentialCoordinates_of_model N hI (dynkin C.ideal N)
        exact ⟨nilpotentModelOfPolynomialIdeal C P⟩
  exact hmain (finrank ℝ L) L rfl hnil

theorem nilpotentLieExistenceInput_of_dynkin
    (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L] :
    NilpotentLieExistenceInput L := by
  let b := Module.finBasis ℝ L
  let : NormedAddCommGroup L := NormedAddCommGroup.induced L _ b.equivFun b.equivFun.injective
  let : NormedSpace ℝ L := NormedSpace.induced ℝ L _ b.equivFun
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup L), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ L), (inferInstance : LieAlgebra ℝ L) with }
  exact nilpotentLieModel_of_dynkin dynkin L

end PolycyclicRecognition

end

end OAI
