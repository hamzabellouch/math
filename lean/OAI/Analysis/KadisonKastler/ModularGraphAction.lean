import OAI.Analysis.KadisonKastler.ModularFrequencyBridge

namespace OAI

/-! # A common modular action from uniform rescaled graph comparison -/

namespace KadisonKastler

open MeasureTheory
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem modularComparisonField_continuous
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω) (x : H) :
    Continuous (fun t => (modularComparisonField m.group n.group t : H →L[ℂ] H) x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs (y : H) : Continuous (fun s : ℝ =>
      (star (m.group (Multiplicative.ofAdd s)) : H →L[ℂ] H) y) := by
    simpa only [← Unitary.coe_star, regularGroup_star_eq, Function.comp_def] using
      (m.continuous y).comp continuous_neg
  exact tendsto_mul_contractions
    (fun s : ℝ => (n.group (Multiplicative.ofAdd s) : H →L[ℂ] H))
    (fun s : ℝ => (star (m.group (Multiplicative.ofAdd s)) : H →L[ℂ] H))
    (n.group (Multiplicative.ofAdd t) : H →L[ℂ] H)
    (star (m.group (Multiplicative.ofAdd t)) : H →L[ℂ] H)
    (fun s => norm_unitary_le_one _) (fun y => (n.continuous y).tendsto t)
    (fun y => (hs y).tendsto t) x

theorem modularComparisonField_star_continuous
    {M N : VonNeumannAlgebra H} {Ω : H}
    (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω) (x : H) :
    Continuous (fun t =>
      ((star (modularComparisonField m.group n.group t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x) := by
  simpa only [modularComparisonField, star_mul, star_star] using
    modularComparisonField_continuous n m x

local instance graphActionOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance graphActionStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The graph estimate now supplies both frequency defects. The uniform
tolerance and linear conjugacy constant precede all representation data. -/
theorem uniform_common_action_of_rescaled_graphs
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
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ γ0 K : ℝ, 0 < γ0 ∧ 0 < K ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (Ω : H) (m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
        (J : H ≃ₗᵢ⋆[ℂ] H),
      (∀ t, PublishedMultiplicationCorrection
        (unitaryConjugateAlgebra (modularComparisonField m.group n.group t) M)) →
      ∀ γ : ℝ, 0 < γ → γ < γ0 → kkDistance M N < γ →
      (∀ c : ℝ, 0 < c →
        ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ B * γ) →
      ∃ q : unitary (H →L[ℂ] H), ‖(q : H →L[ℂ] H) - 1‖ ≤ K * γ ∧
        ∀ t, Conjugates (n.group t) (unitaryConjugateAlgebra q M)
          (unitaryConjugateAlgebra q M) := by
  let C := (1 + Real.exp (-(1 / 2 : ℝ))) / (1 - Real.exp (-(1 / 2 : ℝ)))
  have hC : 0 ≤ C := by
    have h : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by positivity) (by linarith)
  obtain ⟨γ0, K, hγ0, hK, h⟩ := uniform_common_action_of_frequency_defects
    hSpectral hCompare hSakai hDistance hHardy hNest hRealSpectral hDiagonal
    (mul_nonneg hC hB)
  refine ⟨γ0, K, hγ0, hK, ?_⟩
  intro H _ _ _ _ _ M N hM Ω m n J hCorrection γ hγ hsmall hgap hgraph
  have he : 0 ≤ B * γ := mul_nonneg hB hγ.le
  have hcuts := norm_modular_separated_cuts_le m n J he hgraph
  have hgraph' (c : ℝ) (hc : 0 < c) :
      ‖rescaledGraphProjection N J Ω c - rescaledGraphProjection M J Ω c‖ ≤ B * γ := by
    simpa only [norm_sub_rev] using hgraph c hc
  have hcuts' := norm_modular_separated_cuts_le n m J he hgraph'
  have hF := frequencyDefectBound_of_modular_cuts m n
    (modularComparisonField_continuous m n) (mul_nonneg hC he) hcuts
  have hG := frequencyDefectBound_of_modular_cuts n m
    (modularComparisonField_continuous n m) (mul_nonneg hC he) hcuts'
  rw [← mul_assoc] at hF hG
  apply h H M N hM m.group n.group m.normalizes n.normalizes
    (modularComparisonField_continuous m n) (modularComparisonField_star_continuous m n)
    hCorrection γ hγ hsmall hF ?_ hgap
  have hs : (fun t => star (modularComparisonField m.group n.group t)) =
      modularComparisonField n.group m.group := by
    funext t
    simp only [modularComparisonField, star_mul, star_star]
  simpa only [hs] using hG

end

end KadisonKastler

end OAI
