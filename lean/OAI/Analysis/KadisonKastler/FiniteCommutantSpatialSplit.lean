import OAI.Analysis.KadisonKastler.II1CommutantSpatialSplit
import OAI.Analysis.KadisonKastler.FiniteTypeICommutantSpatialSplit

namespace OAI

/-! # Spatial splitting for a finite factor commutant in every representation -/

namespace KadisonKastler

noncomputable section

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

theorem exists_selfAdjoint_split_of_finite_factor_commutant
    (M : VonNeumannAlgebra H) (hN : ScalarCenter M.commutant)
    (hfinite : FiniteProjectionIn M.commutant 1)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  by_cases ht : IsTypeIFactor M.commutant
  · exact exists_selfAdjoint_split_of_finite_typeI_commutant M ht hfinite T hTsa hT
  · exact exists_selfAdjoint_split_of_II1_commutant M
      (isII1Factor_of_finite_of_not_typeI hN zero_ne_one hfinite ht) T hTsa hT

end

end KadisonKastler

end OAI
