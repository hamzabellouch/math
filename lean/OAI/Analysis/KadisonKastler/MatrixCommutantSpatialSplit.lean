import OAI.Analysis.KadisonKastler.AbelianDerivationAveraging
import OAI.Analysis.KadisonKastler.MatrixAveraging

namespace OAI

/-! # Spatial splitting across a full finite matrix commutant -/

namespace KadisonKastler

noncomputable section

open Generator

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

theorem exists_selfAdjoint_split_of_matrix_commutant
    (M : VonNeumannAlgebra H) (E : MatrixUnitSystem ι (H →L[ℂ] H))
    (hE : E.algebra ≤ M.commutant.toStarSubalgebra)
    (hfull : M.commutant.toStarSubalgebra ≤ E.algebra)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  let S := matrixUnitAverage E T
  have hSM : S ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact (matrixUnitAverage_commutes E T a (hfull ha)).eq
  have hSsa : IsSelfAdjoint S := finiteUnitaryAverage_selfAdjoint _ hTsa
  have hSn : ‖S‖ ≤ ‖T‖ := norm_finiteAverage_le
    (fun g => unitaryConj (matrixUnitSignedRepresentation E g) T)
    (fun _ => (norm_unitaryConj _ _).le)
  have hdiff : S - T ∈ M.commutant := by
    have he : S - T = finiteAverage (fun g : SignedPermutation ι =>
        unitaryConj (matrixUnitSignedRepresentation E g) T - T) := by
      rw [finiteAverage_sub, finiteAverage_const]
      rfl
    rw [he]
    apply M.commutant.toStarSubalgebra.smul_mem
    apply M.commutant.toStarSubalgebra.sum_mem
    intro g _
    exact unitaryConj_sub_mem_commutant_of_preserves M T hT _
      (hE (matrixUnitSignedRepresentation_mem E g))
  refine ⟨S, hSM, hSsa, hSn, ?_⟩
  change T - S ∈ M.commutant.toSubalgebra
  simpa only [neg_sub] using M.commutant.neg_mem hdiff

end

end KadisonKastler

end OAI
