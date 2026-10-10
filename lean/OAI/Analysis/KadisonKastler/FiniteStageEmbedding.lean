import OAI.Analysis.KadisonKastler.LocalizedMatrixChainEmbedding
import OAI.Analysis.KadisonKastler.IncreasingMatrixPreparation

namespace OAI

/-! # Embeddings for the matrix stages used by the stability proof -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

/-- A nonzero full matrix representation has a nonempty index set. -/
theorem matrixUnits_index_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (H →L[ℂ] H)) : Nonempty ι := by
  by_contra h
  have hz : ∑ i, E.entry i i = 0 :=
    Finset.sum_eq_zero (fun i _ => False.elim (h ⟨i⟩))
  exact zero_ne_one (hz.symm.trans E.total)

/-- The concrete matrix-unit formulation needs no injectivity or embedding input. -/
theorem exists_localized_unitary_matrixUnits_embedding
    (s : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (s n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    {R N : VonNeumannAlgebra H}
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    {γ : ℝ} (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152) (hnear : NearInclusion R N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (w : H →L[ℂ] H) ∈ generatedVonNeumannAlgebra (R.toStarSubalgebra ⊔ N.toStarSubalgebra) ∧
      (∀ x ∈ R, unitaryConj w x ∈ N) ∧ ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ := by
  let F : ∀ n, FullMatrixFrame (E n).algebra := fun n =>
    FullMatrixFrame.ofUnits (E n) (Classical.choice (matrixUnits_index_nonempty (E n)))
  subst R
  exact exists_localized_unitary_matrixChain_embedding F hmono hγ hsmall hnear

/-- The finite-stage formulation preserves the actual source algebra and the
location in the join with the target. -/
theorem exists_localized_unitary_finiteStage_embedding
    {M N : VonNeumannAlgebra H} (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    {γ : ℝ} (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 1152)
    (hnear : NearInclusion (FiniteMatrixStage.generatedVonNeumann A) N γ) :
    ∃ w : unitary (H →L[ℂ] H),
      (w : H →L[ℂ] H) ∈ generatedVonNeumannAlgebra
        ((FiniteMatrixStage.generatedVonNeumann A).toStarSubalgebra ⊔ N.toStarSubalgebra) ∧
      (∀ x ∈ FiniteMatrixStage.generatedVonNeumann A, unitaryConj w x ∈ N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * γ :=
  exists_localized_unitary_matrixUnits_embedding (fun n => (A n).size)
    (matrixStageConcreteUnits A) (by simpa only [matrixStageConcreteUnits_algebra] using hA)
    (generated_matrixStages_eq A hA) hγ hsmall hnear

/-- Put the actual increasing matrix closure into common position. The
existing downstream constants are retained. -/
theorem exists_common_matrixStage_neighbor_of_kkDistance_lt
    {M N : VonNeumannAlgebra H} (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1 / 1152) (hgap : kkDistance M N < t) :
    ∃ w : unitary (H →L[ℂ] H),
      FiniteMatrixStage.generatedVonNeumann A ≤ unitaryConjugateAlgebra (star w) N ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * t ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤
        kkDistance M N + 2 * ‖(w : H →L[ℂ] H) - 1‖ := by
  obtain ⟨w, _, hw, hn⟩ := exists_localized_unitary_finiteStage_embedding A hA ht hsmall
    (nearInclusion_mono_left (FiniteMatrixStage.generatedVonNeumann_le A)
      (nearInclusion_of_kkDistance_lt hgap))
  refine ⟨w, le_unitaryConjugateAlgebra_star w hw, by linarith, ?_⟩
  have hstar : ‖((star w : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(w : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using
      norm_star ((w : H →L[ℂ] H) - 1)
  simpa only [hstar] using
    (kkDistance_conjugate_le (M := M) (conjugates_unitaryConjugateAlgebra (star w) N))

end

end KadisonKastler

end OAI
