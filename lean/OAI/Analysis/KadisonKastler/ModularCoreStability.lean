import OAI.Analysis.KadisonKastler.ModularGraphAction
import OAI.Analysis.KadisonKastler.CompleteMapTensorGap
import OAI.Analysis.KadisonKastler.MatrixNearInclusion
import OAI.Analysis.KadisonKastler.RegularTensorConjugation
import OAI.Analysis.KadisonKastler.RegularCoreModulus
import OAI.Analysis.KadisonKastler.RealNestDistanceConstruction

namespace OAI

/-! # Completing modular graph stability by descent through the regular core

The source core belongs to the neighboring modular group.
The tensor gap is proved from the same complete maps used for graph
comparison and is propagated through the small action alignment.
-/

namespace KadisonKastler

noncomputable section

universe u

local instance modularCoreOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance modularCoreStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- The modular representation and source-core type are explicit hypotheses
for descent through the regular core. -/
structure ModularCorePublishedInputs : Prop where
  finite : FiniteFactorPublishedInputs.{u}
  coreCommutant : PublishedRegularCommutant.{u}
  realSpectral : PublishedRealSpectralCommutant.{u}
  diagonal : PublishedRealDiagonalDecomposition.{u}
  copies : PublishedProperInfiniteProjectionCopies.{u}
  spectral : PublishedVonNeumannSpectralCut.{u}
  comparison : PublishedTypeIIIProjectionComparison.{u}
  sakai : PublishedSimpleDerivationInner.{u}
  hardy : PublishedHardyMultiplierEvaluation.{u}
  correction : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H), PublishedMultiplicationCorrection M

theorem uniform_modular_graph_strong_stability
    (h : ModularCorePublishedInputs.{u}) {B : ℝ} (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (Ω : H) (_m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
        (J : H ≃ₗᵢ⋆[ℂ] H),
      TypeIIInfinityFactor (regularCoreAlgebra n.group n.continuous N) →
      ∀ (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H)) (G : Algebra N →ₗ[ℂ] (H →L[ℂ] H)),
      (∀ x, F x ∈ N) → (∀ x, G x ∈ M) →
      ∀ γ : ℝ, 0 < γ → γ < δ → kkDistance M N < γ →
      CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ →
      CompletelyBoundedBy (N.toStarSubalgebra.subtype.toAlgHom.toLinearMap - G) γ →
      (∀ c : ℝ, 0 < c →
        ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ B * γ) →
      NearConjugacy M N ε := by
  obtain ⟨γ0, K, hγ0, hK, haction⟩ := uniform_common_action_of_rescaled_graphs
    h.spectral h.comparison h.sakai (fun H _ _ _ M => publishedBlockCommutantApproximation (Algebra M) H)
    h.hardy publishedRealNestDistance h.realSpectral h.diagonal
    hB
  obtain ⟨t, ht, hcore⟩ := uniform_regularCore_strong_stability h.finite h.coreCommutant
    h.realSpectral h.diagonal h.copies (half_pos hε)
  have hA : 0 < 2 + 2 * K := by positivity
  refine ⟨min γ0 (min (t / (2 + 2 * K)) (ε / (2 * K))),
    lt_min hγ0 (lt_min (div_pos ht hA) (div_pos hε (by positivity))), ?_⟩
  intro H _ _ _ _ _ M N hM Ω m n J hNcore F G hFN hGM γ hγ hsmall hgap hF hG hgraph
  obtain ⟨q, hq, hqaction⟩ := haction H M N hM Ω m n J
    (fun _ => h.correction H _) γ hγ (hsmall.trans_le (min_le_left _ _)) hgap hgraph
  let P := unitaryConjugateAlgebra q M
  have htγ : (2 + 2 * K) * γ < t := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hx' := (lt_div_iff₀ hA).mp hx
    nlinarith
  have hqt : K * γ < ε / 2 := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    have hx' := (lt_div_iff₀ (by positivity : 0 < 2 * K)).mp hx
    linarith
  have htensor : kkDistance (regularTensorAlgebra N) (regularTensorAlgebra P) < t := by
    have hg := kkDistance_regularTensorAlgebra_le_of_completely_close_maps M N F G
      hFN hGM hγ.le hF hG
    rw [kkDistance_comm] at hg
    exact (kkDistance_regularTensor_conjugate_le M N q).trans_lt
      (by nlinarith)
  have hgapP : kkDistance N P < t := by
    have hg := kkDistance_conjugate_le (M := N) (conjugates_unitaryConjugateAlgebra q M)
    rw [kkDistance_comm N M] at hg
    exact hg.trans_lt (by nlinarith)
  have hv := hcore H N P (h.correction H N) (publishedBlockCommutantApproximation (Algebra N) H)
    n.group n.continuous
    (fun s x hx => by
      have hs := n.normalizes s
      change unitaryConj (n.group s) x ∈ (N : Set (H →L[ℂ] H))
      rw [← hs]
      exact Set.mem_image_of_mem _ hx)
    (fun s x hx => by
      have hs := hqaction s
      change unitaryConj (n.group s) x ∈
        (unitaryConjugateAlgebra q M : Set (H →L[ℂ] H))
      rw [← hs]
      exact Set.mem_image_of_mem _ hx)
    hNcore htensor hgapP
  have hMP : NearConjugacy M P (ε / 2) :=
    ⟨q, conjugates_unitaryConjugateAlgebra q M, hq.trans_lt hqt⟩
  simpa only [add_halves] using hMP.trans hv.symm


/-- The same original-space conclusion under actual matrix unit-ball proximity.
No global linear selection of approximants is required. -/
theorem uniform_modular_matrix_graph_strong_stability
    (h : ModularCorePublishedInputs.{u}) {B : ℝ} (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (Ω : H) (_m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
        (J : H ≃ₗᵢ⋆[ℂ] H),
      TypeIIInfinityFactor (regularCoreAlgebra n.group n.continuous N) →
      ∀ γ : ℝ, 0 < γ → γ < δ → kkDistance M N < γ →
      MatrixNearInclusion M N γ → MatrixNearInclusion N M γ →
      (∀ c : ℝ, 0 < c →
        ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ B * γ) →
      NearConjugacy M N ε := by
  obtain ⟨γ0, K, hγ0, hK, haction⟩ := uniform_common_action_of_rescaled_graphs
    h.spectral h.comparison h.sakai (fun H _ _ _ M => publishedBlockCommutantApproximation (Algebra M) H)
    h.hardy publishedRealNestDistance h.realSpectral h.diagonal
    hB
  obtain ⟨t, ht, hcore⟩ := uniform_regularCore_strong_stability h.finite h.coreCommutant
    h.realSpectral h.diagonal h.copies (half_pos hε)
  have hA : 0 < 2 + 2 * K := by positivity
  refine ⟨min γ0 (min (t / (2 + 2 * K)) (ε / (2 * K))),
    lt_min hγ0 (lt_min (div_pos ht hA) (div_pos hε (by positivity))), ?_⟩
  intro H _ _ _ _ _ M N hM Ω m n J hNcore γ hγ hsmall hgap hMN hNM hgraph
  obtain ⟨q, hq, hqaction⟩ := haction H M N hM Ω m n J
    (fun _ => h.correction H _) γ hγ (hsmall.trans_le (min_le_left _ _)) hgap hgraph
  let P := unitaryConjugateAlgebra q M
  have htγ : (2 + 2 * K) * γ < t := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hx' := (lt_div_iff₀ hA).mp hx
    nlinarith
  have hqt : K * γ < ε / 2 := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    have hx' := (lt_div_iff₀ (by positivity : 0 < 2 * K)).mp hx
    linarith
  have htensor : kkDistance (regularTensorAlgebra N) (regularTensorAlgebra P) < t := by
    have hg := MatrixNearInclusion.regularTensor_gap hMN hNM hγ.le
    rw [kkDistance_comm] at hg
    exact (kkDistance_regularTensor_conjugate_le M N q).trans_lt
      (by nlinarith)
  have hgapP : kkDistance N P < t := by
    have hg := kkDistance_conjugate_le (M := N) (conjugates_unitaryConjugateAlgebra q M)
    rw [kkDistance_comm N M] at hg
    exact hg.trans_lt (by nlinarith)
  have hv := hcore H N P (h.correction H N) (publishedBlockCommutantApproximation (Algebra N) H)
    n.group n.continuous
    (fun s x hx => by
      have hs := n.normalizes s
      change unitaryConj (n.group s) x ∈ (N : Set (H →L[ℂ] H))
      rw [← hs]
      exact Set.mem_image_of_mem _ hx)
    (fun s x hx => by
      have hs := hqaction s
      change unitaryConj (n.group s) x ∈
        (unitaryConjugateAlgebra q M : Set (H →L[ℂ] H))
      rw [← hs]
      exact Set.mem_image_of_mem _ hx)
    hNcore htensor hgapP
  have hMP : NearConjugacy M P (ε / 2) :=
    ⟨q, conjugates_unitaryConjugateAlgebra q M, hq.trans_lt hqt⟩
  simpa only [add_halves] using hMP.trans hv.symm

end

end KadisonKastler

end OAI
