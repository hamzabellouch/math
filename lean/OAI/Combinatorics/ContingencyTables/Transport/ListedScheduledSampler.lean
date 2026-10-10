import OAI.Combinatorics.ContingencyTables.Transport.ListedBooleanDraw
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBinaryParameters
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperFiniteSampler

namespace OAI

/-! # Accuracy of the fully computed listed sampler schedule -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

variable (hPL : PublishedInputs.FiniteBoxPrekopaLeindler
  (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
variable (hCheeger : PublishedInputs.FiniteCheeger
  (GridBoundary.Grid (I := Fin (largeTailCount r ((dimensionAllowance (I := Fin m) (J := Fin n))^20)*
    largeTailCount c ((dimensionAllowance (I := Fin m) (J := Fin n))^20)))
    (4*(dimensionAllowance (I := Fin m) (J := Fin n))^8)))

include hPL hCheeger

/-- The executable, canonically initialized completion subroutine satisfies
exactly the three-error budget from the manuscript. -/
theorem listedScheduledDraw_accuracy (htotal : (∑ i,r i)=∑ j,c j)
    (x : PaperStates r c) (fallback : Table r c) (k : ℕ) (hk : 1≤k) :
    let _ : Nonempty (Table r c) := ⟨fallback⟩
    (variation (mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c k) → Bool))
      (listedOuterDraw r c e hr hc b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1
        x (outerSteps d b k) (outerTrials d k) fallback))
      (uniformLaw (α := Table r c)):ℝ)≤1/(2:ℝ)^k := by
  let : Nonempty (Table r c) := ⟨fallback⟩
  let : Nonempty (PaperStates r c) := ⟨x⟩
  dsimp only
  rw [listedOuterDraw_law r c e hr hc b (outerAccuracy d b k)
    (smallBinaryLength_parameters r c).1 htotal]
  have hv := listedOuterLaw_variation r c hr hc b (outerAccuracy d b k)
    (smallBinaryLength_parameters r c).1 hPL hCheeger htotal x
    (outerSteps d b k) (outerTrials d k) fallback
  have he := outer_total_error d b k (stateBound r c)
    (listed_dimension_fourteen r c hr hc) (smallBinaryLength_parameters r c).2.1 hk
    (smallBinaryLength_parameters r c).2.2
  apply hv.trans
  convert he using 1
  push_cast
  ring

end
end ContingencyTables.SmallGraphProfiles

end OAI
