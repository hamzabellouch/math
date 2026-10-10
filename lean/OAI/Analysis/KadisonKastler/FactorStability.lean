import OAI.Analysis.KadisonKastler.CommonCenterFromFactors
import OAI.Analysis.KadisonKastler.TypeIFactorStability
import OAI.Analysis.KadisonKastler.FiniteFactorApplication
import OAI.Analysis.KadisonKastler.PublishedInfiniteType

namespace OAI

/-! # Reduction of factor stability to the properly infinite case

The type I, finite diffuse and properly infinite cases use one common
minimum tolerance. The infinite-projection theorem identifies the
properly infinite case of a factor with nonfinite identity.
-/

namespace KadisonKastler

noncomputable section

universe u

/-- The properly infinite factor case, with the tolerance uniform over
all separable representations. -/
def UniformProperInfiniteFactorStability : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H]
      (M N : VonNeumannAlgebra H), ScalarCenter M → ScalarCenter N →
      ProperlyInfiniteIdentity M → kkDistance M N < δ → NearConjugacy M N ε

private theorem nearConjugacy_of_subsingleton
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Subsingleton H] (M N : VonNeumannAlgebra H) {ε : ℝ} (hε : 0 < ε) :
    NearConjugacy M N ε := by
  have hMN : M = N := by
    apply le_antisymm
    · intro x _
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx]
      exact N.zero_mem
    · intro x _
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx]
      exact M.zero_mem
  subst N
  exact nearConjugacy_self M hε

/-- The full factor assertion follows from the type I, II₁ and properly
infinite cases. Zero-dimensional
representations are included in the conclusion. -/
theorem uniformFactorStability_of_properlyInfinite
    (hInfinite : UniformProperInfiniteFactorStability.{u})
    (hFinite : FiniteFactorPublishedInputs.{u})
    (_hTypeI : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
      PublishedTypeIInjectivity (H := H))
    (hProper : PublishedInfiniteFactorProperlyInfinite.{u}) :
    UniformFactorStability.{u} := by
  classical
  intro ε hε
  obtain ⟨δI, hδI, hI⟩ := uniform_separable_typeI_strong_stability.{u} hε
  obtain ⟨δII, hδII, hII⟩ := uniform_II1_strong_stability hFinite hε
  obtain ⟨δPI, hδPI, hPI⟩ := hInfinite ε hε
  refine ⟨min δI (min δII δPI), lt_min hδI (lt_min hδII hδPI), ?_⟩
  intro H _ _ _ _ M N hM hN hgap
  rcases subsingleton_or_nontrivial H with hH | hH
  · let : Subsingleton H := hH
    exact nearConjugacy_of_subsingleton M N hε
  · let : Nontrivial H := hH
    by_cases htype : IsTypeIFactor M
    · exact hI H M N htype
        (hgap.trans_le (min_le_left _ _))
    · by_cases hfinite : FiniteProjectionIn M 1
      · have hII1 := isII1Factor_of_finite_of_not_typeI hM
          (show (0 : H →L[ℂ] H) ≠ 1 from zero_ne_one) hfinite htype
        exact hII H M N hII1
          ((hgap.trans_le (min_le_right _ _)).trans_le (min_le_left _ _))
      · exact hPI H M N hM hN (hProper H M hM hfinite)
          ((hgap.trans_le (min_le_right _ _)).trans_le (min_le_right _ _))

end

end KadisonKastler

end OAI
