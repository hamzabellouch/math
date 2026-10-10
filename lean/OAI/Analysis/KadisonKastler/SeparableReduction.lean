import OAI.Analysis.KadisonKastler.SeparableTests
import OAI.Analysis.KadisonKastler.GeneratedAlgebraGap
import OAI.Analysis.KadisonKastler.LocalCoefficientTests
import OAI.Analysis.KadisonKastler.FiniteCoefficientTests
import OAI.Analysis.KadisonKastler.StabilityStatement

namespace OAI

/-! # Reduction of the universal theorem to separable Hilbert spaces

Local restrictions to separable reducing spaces give finite coefficient
approximants and then a conjugacy on the original Hilbert space.
The tolerance precedes every ambient space.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

universe u

local instance reductionFactorOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance reductionFactorStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- The separable-Hilbert-space intermediate conclusion of §9. -/
def SeparableStrongStability : Prop :=
  ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [SeparableSpace H], ∀ M N : VonNeumannAlgebra H,
        kkDistance M N < δ → NearConjugacy M N a

theorem finiteCoefficientConjugations_of_separable_bound
    (hK : PublishedKaplanskyDensity.{u}) {a δ : ℝ}
    (hsep : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [SeparableSpace K], ∀ P Q : VonNeumannAlgebra K,
        kkDistance P Q < δ → NearConjugacy P Q a)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M N : VonNeumannAlgebra H) (hgap : kkDistance M N < δ) :
    FiniteCoefficientConjugations M N a := by
  classical
  intro E V k
  obtain ⟨g, hgapg, hgδ⟩ := exists_between hgap
  let E' : Finset (H →L[ℂ] H) := E.image Subtype.val
  have hE' : ∀ x ∈ E', x ∈ M := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  obtain ⟨A, B, K, hAc, hBc, _, _, _, hBN, hEA, _, hAB,
      hKc, hKs, hVK, hAK, hBK⟩ :=
    exists_near_separable_tests M N E' ∅ V hE' (by simp) hgapg
  let : CompleteSpace K := hKc.completeSpace_coe
  let : SeparableSpace K := hKs
  let P := generatedVonNeumannAlgebra (reducingRestriction K A hAK).range
  let Q := generatedVonNeumannAlgebra (reducingRestriction K B hBK).range
  have hPQ : kkDistance P Q < δ :=
    ((kkDistance_generated_restriction_le hK K A B hAK hBK hAc hBc).trans_lt hAB).trans hgδ
  obtain ⟨v, hv, hva⟩ := hsep K P Q hPQ
  refine ⟨cornerUnitary K v, (norm_cornerUnitary_sub_one K v).le.trans hva.le, ?_⟩
  intro x hx
  let xA : A := ⟨x.val, hEA x.val (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
  have hxP : reducingRestriction K A hAK xA ∈ P :=
    subset_generatedVonNeumannAlgebra _ ⟨xA, rfl⟩
  have hxQ : unitaryConj v (reducingRestriction K A hAK xA) ∈ Q := by
    change unitaryConj v (reducingRestriction K A hAK xA) ∈ (Q : Set (K →L[ℂ] K))
    rw [← hv]
    exact ⟨_, hxP, rfl⟩
  have hxQ' : unitaryConj v (reducingRestriction K A hAK xA) ∈
      Set.centralizer (Set.centralizer (Set.range (reducingRestriction K B hBK))) := by
    change unitaryConj v (reducingRestriction K A hAK xA) ∈
      (generatedVonNeumannAlgebra (reducingRestriction K B hBK).range : Set _) at hxQ
    rw [generatedVonNeumannAlgebra_coe] at hxQ
    exact hxQ
  obtain ⟨b, hb⟩ := exists_original_coefficient_approx K A B hAK hBK v xA hxQ' V hVK
    (show 0 < (1 : ℝ) / (k + 1) by positivity)
  refine ⟨⟨b.val, hBN b.property⟩, ?_⟩
  intro ξ hξ η hη
  exact hb ξ hξ η hη

/-- Stability on arbitrary Hilbert spaces follows from separable stability,
Kaplansky density, multiplication correction, and commutant approximation. -/
theorem universalStrongStability_of_separable
    (hsep : SeparableStrongStability.{u})
    (hK : PublishedKaplanskyDensity.{u})
    (hCorrection : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H, PublishedMultiplicationCorrection M)
    (hCommutant : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    UniversalStrongStability.{u} := by
  intro ε hε
  let a := min (ε / 512) (1 / 8000)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have ha₁ : a ≤ ε / 512 := min_le_left _ _
  have ha₂ : a ≤ 1 / 8000 := min_le_right _ _
  obtain ⟨δ, hδ, hlocal⟩ := hsep a ha
  refine ⟨min δ (1 / 4), lt_min hδ (by norm_num), ?_⟩
  intro H _ _ _ M N hMN
  have htests := finiteCoefficientConjugations_of_separable_bound hK hlocal M N
    (hMN.trans_le (min_le_left _ _))
  obtain ⟨v, hv, hvn⟩ := concrete_unitary_of_finite_coefficient_tests
    (hCorrection H M) (hCommutant H M) ha.le htests
    (show 2 * a < 1 / 1000 by linarith only [ha₂])
    (show (1 / 4 : ℝ) + 2 * a < 1 by linarith only [ha₂])
    (hMN.trans_le (min_le_right _ _))
  exact ⟨v, hv, hvn.trans_lt (by linarith only [ha₁, hε])⟩

end

end KadisonKastler

end OAI
