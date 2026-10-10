import OAI.Combinatorics.ContingencyTables.Sampling.ExactResidualInput
import OAI.Combinatorics.ContingencyTables.Sampling.ExactMatrixTableLaw

namespace OAI

/-! # The executed correction prefixes converge to the exact residual law -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.PhysicalStream

def correctionPrefix (z : DensePrograms.CompletionMargins) (N : ℕ) :
    Experiment (Option DensePrograms.MatrixCode) :=
  OnlineIntegerRetry.prefixExperiment (f := ExactMatrixTrial.trial) (exactMatrixInput z) N

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms OriginalTableBox ResidualMixture FirstSuccess CompletionCounts
open MatchingFPRAS MatchingFPRAS.PhysicalStream
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "D" => correctionPrecision r c
local notation "q" => largeTailCount r (d^20)*largeTailCount c (d^20)

lemma correctionPrefix_failure
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    (correctionPrefix (List.ofFn r,List.ofFn c) N).mean
      (fun o => if o=none then 1 else 0)≤(1/2:ℚ)^N := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  unfold correctionPrefix
  rw [exactMatrixInput_code r c htotal,scheduledResidualCounts_actual r c hPL hCheeger htotal]
  exact ExactMatrixTrial.prefix_failure _ _
    (ExactMatrixTrial.count_weight_pos _ (Nat.mul_pos Fintype.card_pos
      (pow_pos (scheduledTrialDenominator_pos _) _))) N

lemma correctionPrefix_limit
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (X : Table r c) :
    Filter.Tendsto (fun N => ((correctionPrefix (List.ofFn r,List.ofFn c) N).mean
        (fun o => if o=some (matrixCode X.val) then 1 else 0):ℝ))
      Filter.atTop (nhds ((residualMass
        (mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c (2*D)) → Bool))
          (scheduledTableDraw r c htotal (2*D))) (1/(2:ℚ)^D) X):ℝ)) := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  unfold correctionPrefix
  rw [exactMatrixInput_code r c htotal,scheduledResidualCounts_actual r c hPL hCheeger htotal]
  have ht := ExactMatrixTrial.table_prefix_limit r c
    (IntegerResidualCorrection.law (scheduledCountsLaw r c htotal (2*D)) (2^D)
      (pow_pos (scheduledTrialDenominator_pos _) _) (by positivity)
      (scheduledCounts_domination r c hPL hCheeger htotal))
    (Nat.mul_pos Fintype.card_pos (pow_pos (scheduledTrialDenominator_pos _) _))
    (GreedyFeasibleTable.table r c htotal) X
  rw [IntegerResidualCorrection.law_mass,scheduledCountsLaw_law] at ht
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht

/-- The ordinary draw and correction prefixes have uniform limiting table mass. -/
theorem corrected_prefix_limit
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid (I := Fin q) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (X : Table r c) :
    Filter.Tendsto (fun N =>
      (1-1/(2:ℝ)^D)*
        ((mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c (2*D)) → Bool))
          (scheduledTableDraw r c htotal (2*D))).mass X:ℝ)+
      (1/(2:ℝ)^D)*((correctionPrefix (List.ofFn r,List.ofFn c) N).mean
        (fun o => if o=some (matrixCode X.val) then 1 else 0):ℝ))
      Filter.atTop (nhds ((Fintype.card (Table r c):ℝ)⁻¹)) := by
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  have ht := (Filter.Tendsto.const_mul (1/(2:ℝ)^D)
    (correctionPrefix_limit r c hPL hCheeger htotal X)).const_add
    ((1-1/(2:ℝ)^D)*
      ((mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c (2*D)) → Bool))
        (scheduledTableDraw r c htotal (2*D))).mass X:ℝ))
  have he := congrArg (fun x : ℚ => (x:ℝ))
    (ResidualMixture.mixture_exact
      (mapLaw (uniformLaw (α := Fin (finiteSamplerBits r c (2*D)) → Bool))
        (scheduledTableDraw r c htotal (2*D)))
      (show (1/(2:ℚ)^D)≠0 by positivity) X)
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,
    Rat.cast_ofNat,uniformMass,Rat.cast_inv,Rat.cast_natCast,one_div] at he
  simp only [one_div] at ht ⊢
  rw [he] at ht
  exact ht

end
end ContingencyTables.SmallGraphProfiles

end OAI
