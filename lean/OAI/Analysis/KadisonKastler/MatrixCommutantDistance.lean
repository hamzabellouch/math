import OAI.Analysis.KadisonKastler.CuntzCommutator
import OAI.Analysis.KadisonKastler.PeriodicMatrixAveraging

namespace OAI

/-! # Commutant distance in the presence of countable full matrix units

Finite matrix averaging and Cuntz amplification reduce the estimate to
the commutant-distance formula.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixDistanceOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance matrixDistanceOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance matrixDistanceSourceOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance matrixDistanceSourceStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

private theorem blockDiagonal_commutator (h a : H →L[ℂ] H) :
    innerDerivation (blockDiagonal h h) (blockDiagonal a a) =
      blockDiagonal (h * a - a * h) (h * a - a * h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [innerDerivation_apply, CStarMatrix.mul_apply,
      blockDiagonal, diagonalStarAlgHom_apply]

theorem exists_commutant_approximation_of_complete_bound
    (M : VonNeumannAlgebra H)
    (hPublished : PublishedBlockCommutantApproximation (Algebra M) H)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : CompletelyBoundedBy
      ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) δ)
    (r : ℝ) (hr : δ / 2 < r) :
    ∃ k : H →L[ℂ] H, k ∈ M.commutant ∧ ‖h - k‖ < r := by
  let ρ := M.toStarSubalgebra.subtype
  let π := pairedRepresentation ρ ρ
  let T := blockDiagonal h h
  have hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) δ := by
    apply completelyBoundedBy_of_large_square
    intro n _ X
    have he : matrixBlockSwap (Fin n)
        (CStarMatrix.mapₗ ((innerDerivation T).comp π.toAlgHom.toLinearMap) X) =
        blockDiagonal
          (CStarMatrix.mapₗ ((innerDerivation h).comp ρ.toLinearMap) X)
          (CStarMatrix.mapₗ ((innerDerivation h).comp ρ.toLinearMap) X) := by
      have he' (x : Algebra M) : innerDerivation T (π x) =
          blockDiagonal (h * ρ x - ρ x * h) (h * ρ x - ρ x * h) := by
        rw [pairedRepresentation_apply]
        exact blockDiagonal_commutator h (ρ x)
      apply CStarMatrix.ext
      intro i j
      apply CStarMatrix.ext
      intro v w
      change innerDerivation T (π (X v w)) i j = _
      rw [he']
      fin_cases i <;> fin_cases j <;> rfl
    rw [← norm_matrixBlockSwap (Fin n), he, norm_blockDiagonal, max_self]
    exact hb n n X
  obtain ⟨D, hcomm, hnorm⟩ := hPublished π T δ hδ hcb r hr
  refine ⟨D 0 0, VonNeumannAlgebra.mem_commutant_iff.mpr ?_, ?_⟩
  · intro a ha
    have he := congrArg (fun X : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) => X 0 0)
      (hcomm ⟨a, ha⟩)
    simp only [π, pairedRepresentation_apply, CStarMatrix.mul_apply, Fin.sum_univ_two,
      blockDiagonal, diagonalStarAlgHom_apply] at he
    simpa [ρ] using he.symm
  · have he := matrix_entry_norm_le (D - T) 0 0
    change ‖D 0 0 - h‖ ≤ ‖D - T‖ at he
    rw [norm_sub_rev]
    exact he.trans_lt hnorm

namespace FullMatrixCorner

variable {E : Submodule ℂ H} [CompleteSpace E] (F : FullMatrixCorner E)

theorem exists_commutant_approximation (M : VonNeumannAlgebra H)
    (hPublished : PublishedBlockCommutantApproximation (Algebra M) H)
    (hM : ∀ i j, F.entry i j ∈ M)
    (h : H →L[ℂ] H) (hh : IsSelfAdjoint h) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (r : ℝ) (hr : δ / 2 < r) :
    ∃ k : H →L[ℂ] H, k ∈ M.commutant ∧ ‖h - k‖ < δ + r := by
  obtain ⟨h0, hh0, hc, hdist, hb0⟩ := F.exists_matrixUnit_commuting_average M hM h hh hδ hb
  have hcb := completelyBounded_commutator_of_commuting_cuntz M h0 hh0
    (fun n hn => by
      have : NeZero n := ⟨by omega⟩
      exact ⟨F.finiteCuntz n, F.finiteCuntz_mem n M hM,
        F.commute_finiteCuntz_of_commute_matrixUnits h0 hh0 hc n⟩) hδ hb0
  obtain ⟨k, hk, hclose⟩ := exists_commutant_approximation_of_complete_bound M
    hPublished h0 hδ hcb r hr
  refine ⟨k, hk, ?_⟩
  calc
    ‖h - k‖ ≤ ‖h - h0‖ + ‖h0 - k‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ + r := add_lt_add_of_le_of_lt hdist hclose

end FullMatrixCorner

end

end KadisonKastler

end OAI
