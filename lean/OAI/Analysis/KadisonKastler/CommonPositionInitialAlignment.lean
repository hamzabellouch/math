import OAI.Analysis.KadisonKastler.DiagonalGap
import OAI.Analysis.KadisonKastler.CommonReducingProjection
import OAI.Analysis.KadisonKastler.FaithfulCyclicDiagonalCorner
import OAI.Analysis.KadisonKastler.PreparedPairCorrection

namespace OAI

/-! # Aligning the neighboring factor with the standard cyclic corner -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]

local instance initialAlignmentCountableNontrivial : Nontrivial (CountableHilbertSum H) :=
  nontrivial_of_ne (denseSeparatingUnitVector (H := H)) 0 (by
    intro h
    have hn := norm_denseSeparatingUnitVector (H := H)
    rw [h, norm_zero] at hn
    exact zero_ne_one hn)

omit [Nontrivial H] [TopologicalSpace.SeparableSpace H] in
theorem countableDiagonal_isII1 (M : VonNeumannAlgebra H)
    (hM : IsII1Factor M.toStarSubalgebra) :
    IsII1Factor (countableDiagonalAlgebra M).toStarSubalgebra :=
  isII1Factor_of_starAlgEquiv (countableDiagonalEquiv M) hM
    (traceHilbertVonNeumann_wotClosed (countableDiagonalAlgebra M))

theorem exists_common_cyclic_projection_alignment
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : IsII1Factor N.toStarSubalgebra) {γ : ℝ}
    (hγ : 0 < γ) (hsmall : γ < 1 / 256000000)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    ∃ u : unitary (CountableHilbertSum H →L[ℂ] CountableHilbertSum H),
      (u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) ∈
        (countableDiagonalAlgebra R).commutant ∧
      (faithfulCyclicSpace M).starProjection ∈
        (unitaryConjugateAlgebra (star u) (countableDiagonalAlgebra N)).commutant ∧
      countableDiagonalAlgebra R ≤
        unitaryConjugateAlgebra (star u) (countableDiagonalAlgebra N) ∧
      ‖(u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ ≤
        200000000 * γ := by
  have hgap : kkDistance (countableDiagonalAlgebra M) (countableDiagonalAlgebra N) <
      2 * γ := by
    rw [kkDistance_countableDiagonal]
    exact kkDistance_lt_two_mul_of_nearInclusions hγ hMN hNM
  obtain ⟨u, huR, hup, hun⟩ := exists_unitary_aligning_common_reducing_projection
    (countableDiagonalAlgebra M) (countableDiagonalAlgebra N) (countableDiagonalAlgebra R)
    (countableDiagonalAlgebra_mono hRM) (countableDiagonalAlgebra_mono hRN)
    (countableDiagonal_isII1 N hN) (by positivity : 0 < 2 * γ) (by linarith)
    hgap (faithfulCyclicSpace M).starProjection
    (isStarProjection_starProjection (U := faithfulCyclicSpace M))
    (faithfulCyclic_projection_mem_diagonal_commutant M)
  refine ⟨u, huR, ?_, ?_, by nlinarith⟩
  · have hp := unitaryConj_mem_conjugated_commutant (countableDiagonalAlgebra N) (star u) hup
    simpa only [unitaryConj_star_unitaryConj] using hp
  · apply le_unitaryConjugateAlgebra_star u
    intro r hr
    rw [unitaryConj_eq_self_of_mem_commutant huR hr]
    exact countableDiagonalAlgebra_mono hRN hr

end

end KadisonKastler

end OAI
