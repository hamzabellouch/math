import OAI.Analysis.KadisonKastler.FrequencyNormalizer
import OAI.Analysis.KadisonKastler.ConstructedComparisonNormalizerAlignment
import OAI.Analysis.KadisonKastler.AbelianInvariantMean

namespace OAI

/-! # Common modular actions from the actual frequency defects

The tolerance is fixed before the Hilbert space, the factors and their
actions. The pointwise normalizers are selected with no regularity claim;
the discrete real invariant mean then produces one small change of position.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularComparisonField
    (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (t : ℝ) :
    unitary (H →L[ℂ] H) := V (Multiplicative.ofAdd t) * star (U (Multiplicative.ofAdd t))

def FrequencyDefectBound (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (δ : ℝ) : Prop :=
  ∀ a, ‖(1 - regularFrequencyNest (H := H) a) *
    regularFieldOperator volume (modulatedUnitaryField W)
      (fun x => (modulatedUnitaryField_continuous W hW x).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one W)) *
      regularFrequencyNest (H := H) a‖ ≤ δ

local instance frequencyActionOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance frequencyActionStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem uniform_common_action_of_frequency_defects
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H)
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (hNest : PublishedRealNestDistance.{u})
    (hRealSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ γ0 K : ℝ, 0 < γ0 ∧ 0 < K ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H)),
      (∀ g, Conjugates (U g) M M) → (∀ g, Conjugates (V g) N N) →
      ∀ (hW : ∀ x, Continuous (fun t => (modularComparisonField U V t : H →L[ℂ] H) x))
        (hWs : ∀ x, Continuous (fun t =>
          ((star (modularComparisonField U V t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x)),
      (∀ t, PublishedMultiplicationCorrection
        (unitaryConjugateAlgebra (modularComparisonField U V t) M)) →
      ∀ γ : ℝ, 0 < γ → γ < γ0 →
      FrequencyDefectBound (modularComparisonField U V) hW (D * γ) →
      FrequencyDefectBound (fun t => star (modularComparisonField U V t)) hWs (D * γ) →
      kkDistance M N < γ →
      ∃ q : unitary (H →L[ℂ] H), ‖(q : H →L[ℂ] H) - 1‖ ≤ K * γ ∧
        ∀ g, Conjugates (V g) (unitaryConjugateAlgebra q M)
          (unitaryConjugateAlgebra q M) := by
  obtain ⟨δ0, C, hδ0, hC, hn⟩ := uniform_typeIII_normalizer_from_frequency_defects
    hSpectral hCompare hSakai hDistance hHardy hNest hRealSpectral hDiagonal
  let A : ℝ := D + 3
  have hA : 0 < A := by dsimp [A]; linarith
  refine ⟨min (δ0 / A) (1 / (49152 * C * A)), 3074 * C * A,
    lt_min (div_pos hδ0 hA) (by positivity), by positivity, ?_⟩
  intro H _ _ _ _ _ M N hM U V hU hV hW hWs hCorrection γ hγ hsmall hF hG hgap
  let W := modularComparisonField U V
  have hδ : 0 < A * γ := mul_pos hA hγ
  have hδsmall : A * γ < δ0 := by
    have h := hsmall.trans_le (min_le_left _ _)
    have hm := (lt_div_iff₀ hA).mp h
    nlinarith
  have hgapW (t : ℝ) : kkDistance (unitaryConjugateAlgebra (W t) M) M < A * γ := by
    have h := comparison_unitary_gap M N (U (Multiplicative.ofAdd t))
      (V (Multiplicative.ofAdd t)) (hU _) (hV _)
    change kkDistance (unitaryConjugateAlgebra (W t) M) M ≤ 2 * kkDistance M N at h
    exact h.trans_lt (by dsimp [A]; nlinarith)
  have hF' : FrequencyDefectBound W hW (A * γ) := by
    intro a
    exact (hF a).trans (by dsimp [A]; nlinarith)
  have hG' : FrequencyDefectBound (fun t => star (W t)) hWs (A * γ) := by
    intro a
    exact (hG a).trans (by dsimp [A]; nlinarith)
  have hW0 : W 0 = 1 := by simp [W, modularComparisonField]
  have hWs' : ∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x) := by
    simpa only [Unitary.coe_star] using hWs
  have hnW := hn H M hM W hW0 hW hWs' hCorrection (A * γ) hδ hδsmall hF' hG' hgapW
  choose n hnorm hnear using hnW
  let : TopologicalSpace (Multiplicative ℝ) := ⊥
  let : DiscreteTopology (Multiplicative ℝ) := ⟨rfl⟩
  have hsmall' : 3 * (C * (A * γ)) ≤ 1 / 16384 := by
    have h := hsmall.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ (show 0 < 49152 * C * A by positivity)).mp h
    nlinarith
  obtain ⟨q, hq, haction⟩ := constructed_exists_common_action_of_comparison_normalizers
    M (typeIII_smallNormalizerFactorization hSpectral hCompare hSakai M hM)
    (abelianScalarInvariantMean (Multiplicative ℝ)) U V
    (fun g => hU g) (fun g => n g.toAdd) (fun g => hnorm g.toAdd)
    (by positivity : 0 ≤ C * (A * γ)) hsmall' (fun g => hnear g.toAdd)
  refine ⟨q, hq.trans_eq ?_, haction⟩
  ring

end

end KadisonKastler

end OAI
