import OAI.Analysis.KadisonKastler.ModularCoreStability
import OAI.Analysis.KadisonKastler.PreparedRightGraphRows

namespace OAI

/-! # Original-space stability for a prepared matrix pair

Row comparison, common-action alignment and core descent imply stability.
All tolerances precede the represented algebras. The preparation data and
the neighboring core type are explicit hypotheses.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- Uniform stability once an actual common matrix subalgebra and its
common right action have been prepared. Only matrix unit-ball proximity
is used; no global linear selection of approximants is needed. -/
theorem uniform_prepared_matrix_strong_stability
    (h : ModularCorePublishedInputs.{u}) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N R : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (Ω : H) (_m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
        (J : H ≃ₗᵢ⋆[ℂ] H),
      Function.Involutive J → ‖Ω‖ = 1 →
      TypeIIInfinityFactor (regularCoreAlgebra n.group n.continuous N) →
      ∀ (s : ℕ → ℕ)
        (E : ∀ i, Generator.MatrixUnitSystem (Fin (s i)) (H →L[ℂ] H)),
      Monotone (fun i => (E i).algebra) →
      R = generatedVonNeumannAlgebra (⨆ i, (E i).algebra) → R ≤ M → R ≤ N →
      (∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) →
      (∀ r ∈ R, conjugationOperator J r ∈ M.commutant) →
      (∀ r ∈ R, conjugationOperator J r ∈ N.commutant) →
      (∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω) →
      ∀ γ : ℝ, 0 < γ → γ < δ → kkDistance M N < γ →
      MatrixNearInclusion M N γ → MatrixNearInclusion N M γ → NearConjugacy M N ε := by
  let B : ℝ := 32 * Real.sqrt 2 * 131072
  have hB : 0 ≤ B := by positivity
  obtain ⟨t, ht, hstability⟩ := uniform_modular_matrix_graph_strong_stability h hB hε
  refine ⟨min t (1 / 2), lt_min ht (by norm_num), ?_⟩
  intro H _ _ _ _ _ M N R hM Ω m n J hJ hΩ hNcore s E hmono hR hRM hRN
    hirr hrightM hrightN hvector γ hγ hsmall hgap hMN hNM
  apply hstability H M N hM Ω m n J hNcore γ hγ
    (hsmall.trans_le (min_le_left _ _)) hgap hMN hNM
  intro c hc
  exact norm_preparedRight_graphProjection_sub_le_of_row_approx M N R J hJ Ω hΩ
    s E hmono hR hRM hRN hirr
    (hgap.trans (hsmall.trans_le (min_le_right _ _)))
    hrightM hrightN hvector hγ.le hMN.graphRow_approx hNM.graphRow_approx hc

end

end KadisonKastler

end OAI
