import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBooleanDraw
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBoundedLaw
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperInitialization
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBinaryParameters

namespace OAI

/-! # The initialized finite Boolean sampler on a nonempty large rectangle -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts ResidualMixture FirstSuccess FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
variable {q : ℕ}
variable (e : ({i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀} ×
  {j : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20) // j≠j₀}) ≃ Fin q)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "b" => smallBinaryLength r c
local notation "s" => smallProposalBits (I := I) (J := J)

/-- The exact number of independent input bits used by the initialized
finite experiment. The physical simulation has additional operation cost. -/
abbrev finiteSamplerBits (k : ℕ) : ℕ :=
  let h := outerAccuracy d b k
  let n := outerSteps d b k
  let f := 25*(d+b+h+1)^62
  outerTrials d k*(n*(s+f)+f)

/-- Greedy arithmetic supplies all feasible fallbacks and the starting
state. Each word returns a member of the original margin fibre. -/
def initializedFiniteDraw (k : ℕ) (htotal : (∑ i,r i)=∑ j,c j)
    (a : GridBoundary.Grid (I := Fin q) (4*d^8))
    (bits : Fin (finiteSamplerBits r c k) → Bool) : Table r c :=
  finiteOuterDraw r c i₀ j₀ e b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1 a
    (greedyFibre r c i₀ j₀) (initialJoint r c htotal).1 (outerSteps d b k) (outerTrials d k)
    (GreedyFeasibleTable.reindexed r c htotal) bits

/-- Conditional accuracy of the entire actual finite-word experiment,
with no assumed sampler, starting state, or completion fallback. -/
theorem initializedFiniteDraw_variation (k : ℕ) (hk : 1 ≤ k)
    (htotal : (∑ i,r i)=∑ j,c j)
    (a : GridBoundary.Grid (I := Fin q) (4*d^8))
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8))) :
    let _ : Nonempty (Table r c) := ⟨GreedyFeasibleTable.reindexed r c htotal⟩
    (variation (mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c k) → Bool))
      (initializedFiniteDraw r c i₀ j₀ e k htotal a))
      (uniformLaw (α := Table r c)):ℝ) ≤ 1/(2:ℝ)^k := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.reindexed r c htotal⟩
  let : Nonempty (PaperStates r c) := ⟨(initialJoint r c htotal).1⟩
  dsimp only
  unfold initializedFiniteDraw
  rw [finiteOuterDraw_law r c i₀ j₀ e b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1 a
    (greedyFibre r c i₀ j₀) (initialJoint r c htotal).1 (outerSteps d b k) (outerTrials d k)
    (GreedyFeasibleTable.reindexed r c htotal)]
  exact boundedOuterLaw_variation r c i₀ j₀ e b k (smallBinaryLength_parameters r c).1
    (smallBinaryLength_parameters r c).2.1 hk (smallBinaryLength_parameters r c).2.2
    a (greedyFibre r c i₀ j₀) hPL hCheeger htotal (initialJoint r c htotal).1 _

end
end ContingencyTables.SmallGraphProfiles

end OAI
