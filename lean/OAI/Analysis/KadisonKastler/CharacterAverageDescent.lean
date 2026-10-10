import OAI.Analysis.KadisonKastler.FixedPointGap
import OAI.Analysis.KadisonKastler.AveragedRangeDescent

namespace OAI

/-! # Descent by the character-action average

The concrete crossed-product representation identifies the joint fixed
algebra with the embedded original algebra. Once that actual identity is
available, the scalar character mean supplies the UCP map required for
descent. No statement that its entire ambient range is embedded is used.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

section JointFixedPoints

variable {G L K : Type*} [Group G] [Group L]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem mem_jointFixedPointAlgebra_iff
    (U : G →* unitary (K →L[ℂ] K)) (V : L →* unitary (K →L[ℂ] K))
    (B : VonNeumannAlgebra K) (T : K →L[ℂ] K) :
    T ∈ fixedPointAlgebra V (fixedPointAlgebra U B) ↔
      T ∈ B ∧ (∀ g, unitaryConj (U g) T = T) ∧
        (∀ l, unitaryConj (V l) T = T) := by
  simp only [mem_fixedPointAlgebra_iff, and_assoc]

/-- Joint fixed points do not depend on the order of the two conditions. -/
theorem fixedPointAlgebra_interchange
    (U : G →* unitary (K →L[ℂ] K)) (V : L →* unitary (K →L[ℂ] K))
    (B : VonNeumannAlgebra K) :
    fixedPointAlgebra V (fixedPointAlgebra U B) =
      fixedPointAlgebra U (fixedPointAlgebra V B) := by
  apply VonNeumannAlgebra.ext
  intro T
  simp only [mem_jointFixedPointAlgebra_iff, and_comm]

/-- Commuting conjugation actions restrict to each other's fixed algebra. -/
theorem normalizes_fixedPointAlgebra_of_commuting_actions
    (U : G →* unitary (K →L[ℂ] K)) (V : L →* unitary (K →L[ℂ] K))
    (B : VonNeumannAlgebra K)
    (hB : ∀ l T, T ∈ B → unitaryConj (V l) T ∈ B)
    (hcomm : ∀ g l T, unitaryConj (U g) (unitaryConj (V l) T) =
      unitaryConj (V l) (unitaryConj (U g) T)) :
    ∀ l T, T ∈ fixedPointAlgebra U B →
      unitaryConj (V l) T ∈ fixedPointAlgebra U B := by
  intro l T hT
  obtain ⟨hTB, hTU⟩ := (mem_fixedPointAlgebra_iff U B T).mp hT
  rw [mem_fixedPointAlgebra_iff]
  refine ⟨hB l T hTB, ?_⟩
  intro g
  rw [hcomm, hTU]

end JointFixedPoints

section Descent

universe u v w s

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {G : Type w} [Group G] {L : Type s} [Group L]
  [TopologicalSpace L] [DiscreteTopology L]
  {M N : VonNeumannAlgebra H}

local instance characterDescentOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance characterDescentOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _
local instance characterDescentFactorOrder (P : VonNeumannAlgebra H) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance characterDescentFactorStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- The same proved average, expressed with the spectral-order instances
used by the descent criterion. Its matrix positivity is unchanged. -/
def characterAverage (m : ScalarInvariantMean L) (V : L →* unitary (K →L[ℂ] K)) :
    (K →L[ℂ] K) →CP (K →L[ℂ] K) where
  toLinearMap := by
    letI : PartialOrder (K →L[ℂ] K) := ContinuousLinearMap.instLoewnerPartialOrder
    letI : StarOrderedRing (K →L[ℂ] K) := ContinuousLinearMap.instStarOrderedRing
    exact (m.averageConjugation V).toLinearMap
  map_cstarMatrix_nonneg' n X hX := by
    let : PartialOrder (K →L[ℂ] K) := ContinuousLinearMap.instLoewnerPartialOrder
    let : StarOrderedRing (K →L[ℂ] K) := ContinuousLinearMap.instStarOrderedRing
    exact (m.averageConjugation V).map_cstarMatrix_nonneg X hX

/-- The character average has the exact range property needed on the
conjugated source. Only the joint fixed algebra is identified with `j(N)`. -/
theorem characterAverage_conjugate_mem_range
    (m : ScalarInvariantMean L)
    (U : G →* unitary (K →L[ℂ] K)) (V : L →* unitary (K →L[ℂ] K))
    (A B : VonNeumannAlgebra K)
    (j : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hV : ∀ l T, T ∈ fixedPointAlgebra U B →
      unitaryConj (V l) T ∈ fixedPointAlgebra U B)
    (hjoint : (fixedPointAlgebra V (fixedPointAlgebra U B) : Set (K →L[ℂ] K)) =
      j '' (N : Set (H →L[ℂ] H)))
    (hjM : ∀ x : Algebra M, j x ∈ fixedPointAlgebra U A)
    (z : unitary (K →L[ℂ] K))
    (hz : Conjugates z (fixedPointAlgebra U A) (fixedPointAlgebra U B))
    (x : Algebra M) :
    m.averageConjugation V
        ((z : K →L[ℂ] K) * j x * star (z : K →L[ℂ] K)) ∈
      j '' (N : Set (H →L[ℂ] H)) := by
  rw [← hjoint]
  apply m.averageConjugation_mem_fixed V (fixedPointAlgebra U B) hV
  change unitaryConj z (j x) ∈ (fixedPointAlgebra U B : Set (K →L[ℂ] K))
  rw [← hz]
  exact ⟨j x, hjM x, rfl⟩

/-- A conjugacy of the first fixed algebras descends through the actual
character average to a nearby unitary on the original Hilbert space. -/
theorem concrete_unitary_of_character_average
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (m : ScalarInvariantMean L)
    (U : G →* unitary (K →L[ℂ] K)) (V : L →* unitary (K →L[ℂ] K))
    (A B : VonNeumannAlgebra K)
    (j : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (hj : Function.Injective j)
    (hV : ∀ l T, T ∈ fixedPointAlgebra U B →
      unitaryConj (V l) T ∈ fixedPointAlgebra U B)
    (hjoint : (fixedPointAlgebra V (fixedPointAlgebra U B) : Set (K →L[ℂ] K)) =
      j '' (N : Set (H →L[ℂ] H)))
    (hjM : ∀ x : Algebra M, j x ∈ fixedPointAlgebra U A)
    (hjfix : ∀ l x, unitaryConj (V l) (j x) = j x)
    (z : unitary (K →L[ℂ] K))
    (hz : Conjugates z (fixedPointAlgebra U A) (fixedPointAlgebra U B))
    {g : ℝ} (hgap : kkDistance M N < g)
    (hsmall : 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1 / 1000)
    (hge : g + 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 256 * ‖(z : K →L[ℂ] K) - 1‖ := by
  exact concrete_unitary_of_averaged_range j hj (characterAverage m V) z
    (characterAverage_conjugate_mem_range m U V A B j hV hjoint hjM z hz)
    hCorrection hCommutant (m.averageConjugation_one V)
    (fun x => m.averageConjugation_fixed V (j x) (fun l => hjfix l x))
    hgap hsmall hge

end Descent

end

end KadisonKastler

end OAI
