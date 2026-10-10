import OAI.Analysis.KadisonKastler.CentralConjugacyAssembly
import OAI.Analysis.KadisonKastler.CommonRepresentationGap
import OAI.Analysis.KadisonKastler.CommonCenterReduction

namespace OAI

/-! # The common-center reduction to the uniform factor theorem

Uniform stability of factors passes to algebras with a common center
by constructing nearby separable test algebras, bounding their fibers,
and assembling the factor implementers.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u

local instance {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _

local instance {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- Factor stability with a tolerance independent of the
represented factors. Zero-dimensional representations are allowed. -/
def UniformFactorStability : Prop :=
  ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [SeparableSpace H], ∀ M N : VonNeumannAlgebra H,
        ScalarCenter M → ScalarCenter N → kkDistance M N < δ → NearConjugacy M N a

theorem commonCenterSeparableStability_of_factors
    (hFactor : UniformFactorStability.{u})
    (hCentral : PublishedCentralPairDecomposition.{u})
    (hK : PublishedKaplanskyDensity.{u})
    (hSelect : PublishedUnitaryBorelSelection.{u, u}) :
    CommonCenterSeparableStability.{u} := by
  intro a ha
  obtain ⟨τ, hτ, hlocal⟩ := hFactor (a / 2) (by positivity)
  refine ⟨τ / 2, by positivity, ?_⟩
  intro H _ _ _ _ M N hcenter hgap
  obtain ⟨A, B, hAc, hBc, hAs, hBs, hAM, hBN, hAB⟩ :=
    exists_near_separable_generators M N hgap
  have hMD : M.toStarSubalgebra ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    intro T hT
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hz.2) T hT).symm
  have hND : N.toStarSubalgebra ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    rw [hcenter]
    intro T hT
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hz.2) T hT).symm
  have hAD : A ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    intro T hT
    apply hMD
    rw [← hAM]
    exact subset_generatedVonNeumannAlgebra A hT
  have hBD : B ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    intro T hT
    apply hND
    rw [← hBN]
    exact subset_generatedVonNeumannAlgebra B hT
  obtain ⟨C, hCc, hCs, hAC, hBC, hCD⟩ :=
    exists_closed_separable_common_superalgebra_in A B (concreteCenter M).commutant
      hAs hBs hAD hBD
  obtain ⟨D⟩ := hCentral H M N hcenter A B C hAc hBc hCc hAs hBs hCs hAM hBN hAC hBC hCD
  have hex (n : ℕ) : ∀ᵐ x ∂(D.stratum n).μ,
      ∃ v : unitary ((D.stratum n).K →L[ℂ] (D.stratum n).K),
        Conjugates v
          (generatedVonNeumannAlgebra
            ((D.representation n x).comp (StarSubalgebra.inclusion hAC)).range)
          (generatedVonNeumannAlgebra
            ((D.representation n x).comp (StarSubalgebra.inclusion hBC)).range) ∧
        ‖(v : (D.stratum n).K →L[ℂ] (D.stratum n).K) - 1‖ ≤ a / 2 := by
    filter_upwards [D.factors n] with x hx
    have hd := kkDistance_commonRepresentation_le hK A B C hAc hBc hCc hAC hBC
      (D.representation n x)
    have hdτ : kkDistance
        (generatedVonNeumannAlgebra
          ((D.representation n x).comp (StarSubalgebra.inclusion hAC)).range)
        (generatedVonNeumannAlgebra
          ((D.representation n x).comp (StarSubalgebra.inclusion hBC)).range) < τ := by
      linarith only [hd, hAB, hτ]
    obtain ⟨v, hv, hvn⟩ := hlocal (D.stratum n).K _ _ hx.1 hx.2 hdτ
    exact ⟨v, hv, hvn.le⟩
  obtain ⟨v, hv, hvn⟩ := exists_bounded_conjugacy_from_centralPair hK hSelect
    M N A B C hAc hBc hAs hBs D (by positivity : 0 ≤ a / 2) hex
  exact ⟨v, hv, hvn.trans_lt (by linarith only [ha])⟩

/-- Uniform factor stability, central decomposition and the perturbation
properties give strong stability on arbitrary representations. -/
theorem universalStrongStability_of_factors
    (hFactor : UniformFactorStability.{u})
    (hCentral : PublishedCentralPairDecomposition.{u})
    (hK : PublishedKaplanskyDensity.{u})
    (hSelect : PublishedUnitaryBorelSelection.{u, u})
    (hDix : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H, PublishedDixmierAveraging M)
    (hCorrection : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H, PublishedMultiplicationCorrection M)
    (hCommutant : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    UniversalStrongStability.{u} :=
  universalStrongStability_of_separable
    (separableStrongStability_of_common_center
      (commonCenterSeparableStability_of_factors hFactor hCentral hK hSelect) hDix)
    hK hCorrection hCommutant

end

end KadisonKastler

end OAI
