import OAI.Combinatorics.ContingencyTables.Sampling.AllSamplingSemantics
import OAI.Combinatorics.ContingencyTables.Transport.ListedScheduledSampler

namespace OAI

/-! # Accuracy of the single computed sampler for arbitrary margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess FairBits SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c
local notation "q" => largeTailCount r (d^20)*largeTailCount c (d^20)

/-- The mathematical draw whose code is the output of the single public program. -/
def scheduledTableDraw (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ)
    (bits : Fin (finiteSamplerBits r c k) → Bool) : Table r c :=
  if h : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true then
    listedOuterDraw r c (computedCellEquiv r c)
      ((hasLargeRectangle_spec r c k).mp h).1 ((hasLargeRectangle_spec r c k).mp h).2
      b (outerAccuracy d b k) (smallBinaryLength_parameters r c).1
      (tableState r c (GreedyFeasibleTable.table r c htotal))
      (outerSteps d b k) (outerTrials d k) (GreedyFeasibleTable.table r c htotal) bits
  else
    unitCodeOuterDraw r c (computedCellEquiv r c) (allSmallFibre r c (allSmall_of_no_large r c k h))
      (tableState r c (GreedyFeasibleTable.table r c htotal)) (outerSteps d b k) (outerTrials d k)
      (GreedyFeasibleTable.table r c htotal) (prefixWord (unitCodeBits_le r c k) bits)

theorem samplingMatrixAll_code (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ)
    (bits : Fin (finiteSamplerBits r c k) → Bool) :
    samplingMatrixAll (((List.ofFn r,List.ofFn c),k),List.ofFn bits)=
      matrixCode (scheduledTableDraw r c htotal k bits).val := by
  unfold samplingMatrixAll scheduledTableDraw
  by_cases h : hasLargeRectangle ((List.ofFn r,List.ofFn c),k)=true
  · rw [ite_eq_left h,dite_eq_left h]
    exact samplingMatrix_code r c ((hasLargeRectangle_spec r c k).mp h).1
      ((hasLargeRectangle_spec r c k).mp h).2 htotal k bits
  · rw [ite_eq_right h,dite_eq_right h]
    exact unitSamplingMatrix_code r c (allSmall_of_no_large r c k h) htotal k bits

theorem publicSamplingAll_spec (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ)
    (bits : Fin (finiteSamplerBits r c k) → Bool) :
    publicSamplingAll (Algorithms.encodeSamplingInput r c k,List.ofFn bits)=
      Algorithms.encodeMatrix (scheduledTableDraw r c htotal k bits).val := by
  rw [publicSamplingAll,parsedSampling_spec,samplingMatrixAll_code r c htotal]
  exact GreedyFeasibleTable.printMatrix_ofFn _

private lemma law_uniform_of_subsingleton {Y : Type*} [Fintype Y] [Subsingleton Y]
    [Nonempty Y] (p : RationalLaw Y) : p=uniformLaw (α := Y) := by
  apply RationalLaw.ext
  funext y
  let : Unique Y := ⟨⟨y⟩,fun z => Subsingleton.elim z y⟩
  have ht : p.mass (default : Y)=1 := by simpa using p.total
  have hy : p.mass y=1 := (congrArg p.mass (Subsingleton.elim y default)).trans ht
  simp only [uniformLaw,uniformMass,Fintype.card_unique,Nat.cast_one,div_one,hy]

private lemma variation_uniform_of_subsingleton {Y : Type*} [Fintype Y] [Subsingleton Y]
    [Nonempty Y] (p : RationalLaw Y) : variation p (uniformLaw (α := Y))=0 := by
  rw [law_uniform_of_subsingleton p,variation_self]

/-- Only the two cited published inputs on the completion grid are used.
The small and zero-dimensional branches need neither input. -/
theorem scheduledTableDraw_accuracy
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) (hk : 1≤k) :
    let _ : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
    (variation (mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c k) → Bool))
      (scheduledTableDraw r c htotal k)) (uniformLaw (α := Table r c)):ℝ)≤1/(2:ℝ)^k := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  let : Nonempty (PaperStates r c) := ⟨tableState r c (GreedyFeasibleTable.table r c htotal)⟩
  dsimp only
  unfold scheduledTableDraw
  split_ifs with h
  · exact listedScheduledDraw_accuracy r c (computedCellEquiv r c)
      ((hasLargeRectangle_spec r c k).mp h).1 ((hasLargeRectangle_spec r c k).mp h).2
      hPL hCheeger htotal (tableState r c (GreedyFeasibleTable.table r c htotal))
      (GreedyFeasibleTable.table r c htotal) k hk
  · have hs := allSmall_of_no_large r c k h
    rcases isEmpty_or_nonempty (Fin m) with hm|hm
    · let := hm
      let : Subsingleton (Table r c) := ⟨fun X Y => Subtype.ext (by funext i; exact isEmptyElim i)⟩
      rw [variation_uniform_of_subsingleton,Rat.cast_zero]
      positivity
    · rcases isEmpty_or_nonempty (Fin n) with hn|hn
      · let := hn
        let : Subsingleton (Table r c) := ⟨fun X Y => Subtype.ext (by funext i j; exact isEmptyElim j)⟩
        rw [variation_uniform_of_subsingleton,Rat.cast_zero]
        positivity
      · let := hm
        let := hn
        rw [padded_draw_law,unitCodeOuterDraw_law r c (computedCellEquiv r c) htotal]
        exact unitOuterDraw_accuracy r c hs htotal k hk (allSmallFibre r c hs)
          (tableState r c (GreedyFeasibleTable.table r c htotal)) (GreedyFeasibleTable.table r c htotal)

end
end ContingencyTables.SmallGraphProfiles

end OAI
