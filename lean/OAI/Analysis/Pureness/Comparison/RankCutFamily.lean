import OAI.Analysis.Pureness.Comparison.ThinSpectralSupport

namespace OAI
open scoped BigOperators
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [IsSimpleCStarAlgebra A]

theorem exists_rank_approximating_cut_family
    (hinfinite : ¬ FiniteDimensional ℂ A) {b : A} (hb : 0 ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℕ, 1 ≤ L ∧ ∃ v : ℕ → A, ∃ hv : ∀ j, 0 ≤ v j,
      ∀ τ : TracialState A,
        (τ.toPositiveLinearMap b).re - δ <
          ∑ j ∈ Finset.range L, (τ.spectralSupportMass (v j) (hv j)).toReal ∧
        (∑ j ∈ Finset.range L, (τ.spectralSupportMass (v j) (hv j)).toReal) ≤
          (τ.toPositiveLinearMap b).re := by
  obtain ⟨e, he, hen, henorm, hefull, hesmall⟩ := exists_thin_full_spectral_element hinfinite hδ
  obtain ⟨c, hc, hcm, htrace⟩ := exists_hereditary_trace_compression he hen hb
  obtain ⟨N, hN⟩ := exists_nat_ge ‖c‖
  let L := N + 1
  have hL : ‖c‖ ≤ L := by dsimp [L]; push_cast; linarith
  refine ⟨L, by dsimp [L]; omega, (fun j => positiveCut c (j + 1 : ℕ)),
    (fun j => positiveCut_nonneg c (j + 1 : ℕ)), fun τ => ?_⟩
  have hsmall : (τ.spectralSupportMass c hc).toReal < δ :=
    (τ.hereditary_support_mass_le he hc hcm).trans_lt (hesmall τ)
  have herr := τ.integer_spectral_trace_error hc hL
  have heq : (∑ j ∈ Finset.range L,
      (τ.spectralSupportMass (positiveCut c (j + 1 : ℕ))
        (positiveCut_nonneg c (j + 1 : ℕ))).toReal) =
      ∑ j ∈ Finset.range L,
        (τ.spectralMeasure c hc.isSelfAdjoint (Set.Ioi (j + 1 : ℕ))).toReal := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [τ.positiveCut_support_mass c hc.isSelfAdjoint]
  rw [heq]
  rw [htrace τ] at herr
  exact rank_error_bounds herr.1 herr.2 hsmall
end CuntzComparison

end OAI
