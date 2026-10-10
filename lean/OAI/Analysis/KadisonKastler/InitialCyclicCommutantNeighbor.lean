import OAI.Analysis.KadisonKastler.InitialCyclicNeighbor
import OAI.Analysis.KadisonKastler.ReducingCommutantNear

namespace OAI

/-! # The initial cyclic neighbor with its two-sided commutant bound -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]

local instance cyclicNeighborCountableNontrivial : Nontrivial (CountableHilbertSum H) :=
  nontrivial_of_ne (denseSeparatingUnitVector (H := H)) 0 (by
    intro h
    have hn := norm_denseSeparatingUnitVector (H := H)
    rw [h, norm_zero] at hn
    exact zero_ne_one hn)

theorem exists_initial_cyclic_commutant_neighbor
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N)
    (hM : IsII1Factor M.toStarSubalgebra) (hN : IsII1Factor N.toStarSubalgebra)
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 3200000000)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    ∃ (P : VonNeumannAlgebra (faithfulCyclicSpace M))
      (e : Algebra N ≃⋆ₐ[ℂ] Algebra P),
      IsII1Factor P.toStarSubalgebra ∧
      (∀ r : Algebra R,
        (e (coordinateInclusion hRN r)).val = faithfulCyclicHom M (coordinateInclusion hRM r)) ∧
      (∀ (a : Algebra M) (b : Algebra N), ‖b‖ ≤ 1 →
        ‖faithfulCyclicHom M a - (e b).val‖ ≤ 400000000 * γ + ‖a.val - b.val‖) ∧
      NearInclusion (faithfulCyclicAlgebra M).commutant P.commutant (405000000 * γ) ∧
      kkDistance (faithfulCyclicAlgebra M).commutant P.commutant ≤ 810000000 * γ := by
  exact (exists_common_cyclic_projection_alignment (H := H) M N R hRM hRN hN
    (γ := γ) hγ (by linarith) hMN hNM).elim (fun u hu =>
      (initial_cyclic_neighbor_of_alignment (H := H) M N R hRM hRN hN (γ := γ)
        u hu.1 hu.2.1 hu.2.2.2).elim (fun P hP => hP.elim (fun e he => by
          have hgap : kkDistance (countableDiagonalAlgebra M) (countableDiagonalAlgebra N) <
              2 * γ := by
            rw [kkDistance_countableDiagonal]
            exact kkDistance_lt_two_mul_of_nearInclusions hγ hMN hNM
          have hnear := nearInclusion_reducing_commutants_after_alignment
            (faithfulCyclicSpace M) (countableDiagonalAlgebra M) (countableDiagonalAlgebra N)
            (countableDiagonal_isII1 N hN) (faithfulCyclic_projection_mem_diagonal_commutant M)
            u hu.2.1 hγ hsmall hgap hu.2.2.2
          have hdist := kkDistance_reducing_commutants_after_alignment
            (faithfulCyclicSpace M) (countableDiagonalAlgebra M) (countableDiagonalAlgebra N)
            (countableDiagonal_isII1 M hM) (countableDiagonal_isII1 N hN)
            (faithfulCyclic_projection_mem_diagonal_commutant M) u hu.2.1 hγ hsmall hgap hu.2.2.2
          rw [faithfulCyclic_diagonal_corner_eq, ← he.2.2.2] at hnear hdist
          exact ⟨P, e, he.1, he.2.1, he.2.2.1, hnear, hdist⟩)))

end

end KadisonKastler

end OAI
