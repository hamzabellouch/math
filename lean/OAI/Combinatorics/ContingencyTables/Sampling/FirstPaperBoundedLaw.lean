import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperImplementedLaw

namespace OAI

/-! # The bounded finite sampling law reaches the requested accuracy -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)] [Nonempty (Table r c)]
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
variable {q : ℕ}
variable (e : ({i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀} ×
  {j : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20) // j≠j₀}) ≃ Fin q)

local notation "d" => dimensionAllowance (I := I) (J := J)

/-- The concrete completion draw, literal small transition and repeated
success test have the full error guarantee on nonempty large rectangles.
The physical machine and empty-rectangle branch are separate constructions. -/
theorem boundedOuterLaw_variation (b k : ℕ)
    (hb : Nat.clog 2 (stateBound r c+2) ≤ b) (hdb : d ≤ b) (hk : 1 ≤ k)
    (hC : stateBound r c+1 ≤ 2^b)
    (a : GridBoundary.Grid (I := Fin q) (4*d^8))
    (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : ∑ i,r i=∑ j,c j) (x : PaperStates r c) (z₀ : Table r c) :
    (variation (retryLaw
      (implementedJointLaw r c i₀ j₀ e b (outerAccuracy d b k) hb a fallback x (outerSteps d b k))
      (stateTrial r c) z₀ (outerTrials d k)) (uniformLaw (α := Table r c)):ℝ) ≤ 1/(2:ℝ)^k := by
  have hv := implementedOuterLaw_variation r c i₀ j₀ e b (outerAccuracy d b k) hb a fallback
    hPL hCheeger htotal x (outerSteps d b k) (outerTrials d k) z₀
  have he := outer_total_error d b k (stateBound r c)
    (reference_dimension_fourteen r c _ i₀ j₀) hdb hk hC
  apply hv.trans
  convert he using 1
  push_cast
  ring

end
end ContingencyTables.SmallGraphProfiles

end OAI
