import OAI.LinearAlgebra.MatrixMultiplication.Completion.FiniteRealization
import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.SquareWitness

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionSquareRates

open MatrixMultiplication.Foundation CompletionHierarchyWords CompletionFiniteRealization
open Filter StageHierarchyResources
open scoped BigOperators Topology Classical

variable {A X Y Z : Type} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ)
variable (hD : 0 < ∑ a, counts a)
variable (complete : Function.Injective (labelRecordOf H.labels H.depth))
variable {T : Tensor ℂ X Y Z} {factors d D : ℕ}
variable (source : Tensor.PolynomialApproximation T (3 ^ factors) d D)
variable (supported : ∀ x y z, T x y z ≠ 0 →
  ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)
variable (factors_pos : 0 < factors)

def positiveRealization (n : ℕ) : FiniteMMRealization :=
  realization H counts (n + 1) complete source supported unit factors_pos
    (Nat.mul_pos (Nat.succ_pos n) hD)

def countMass (a : A) : ℝ := (counts a : ℝ) / (∑ a, counts a : ℕ)

private theorem normalize_log (K t population factors : ℕ)
    (_ : 0 < t) (_ : 0 < population) (_ : 0 < factors) :
    Real.log (K : ℝ) / ((factors * (t * population) : ℕ) : ℝ) =
      (Real.log (K : ℝ) / ((t : ℝ) * (population : ℝ))) / (factors : ℝ) := by
  simp only [Nat.cast_mul, div_div]
  congr 1
  ring

theorem multiplicity_rate :
    Tendsto (fun n =>
      Real.log ((positiveRealization H counts hD complete source supported unit factors_pos n).multiplicity : ℝ) /
      ((positiveRealization H counts hD complete source supported unit factors_pos n).occurrences : ℝ))
      atTop (𝓝 (finiteEntropy (countMass counts) / factors)) := by
  have hpop := (tendsto_log_exactWords_card_mul counts hD).comp (tendsto_add_atTop_nat 1)
  have hnormalized := hpop.div_const (factors : ℝ)
  change Tendsto _ atTop (𝓝 (finiteEntropy (countMass counts) / factors)) at hnormalized
  apply hnormalized.congr
  intro n
  symm
  change Real.log (copies H counts (n + 1) : ℝ) /
    ((factors * blocks counts (n + 1) : ℕ) : ℝ) = _
  simp only [copies, blocks, CompletionExecution.realize_label_card H counts (n + 1) complete]
  exact normalize_log _ (n + 1) (∑ a, counts a) factors (Nat.succ_pos n) hD factors_pos

theorem auxiliary_rate :
    Tendsto (fun n =>
      Real.log ((positiveRealization H counts hD complete source supported unit factors_pos n).auxiliaryRank : ℝ) /
      ((positiveRealization H counts hD complete source supported unit factors_pos n).occurrences : ℝ))
      atTop (𝓝 (finiteEntropy (countMass counts) / factors)) := by
  have hrank := (tendsto_log_stageAuxiliaryBudget counts hD H.labels H.depth complete).comp
    (tendsto_add_atTop_nat 1)
  have hnormalized := hrank.div_const (factors : ℝ)
  change Tendsto _ atTop (𝓝 (finiteEntropy (countMass counts) / factors)) at hnormalized
  apply hnormalized.congr
  intro n
  symm
  change Real.log ((CompletionExecution.realize H counts (n + 1)).execution.rankBound : ℝ) /
    ((factors * blocks counts (n + 1) : ℕ) : ℝ) = _
  simp only [CompletionExecution.realize_rankBound, blocks]
  exact normalize_log _ (n + 1) (∑ a, counts a) factors (Nat.succ_pos n) hD factors_pos

theorem volume_rate :
    Tendsto (fun n =>
      Real.log ((positiveRealization H counts hD complete source supported unit factors_pos n).rates.volume : ℝ) /
      ((positiveRealization H counts hD complete source supported unit factors_pos n).occurrences : ℝ))
      atTop (𝓝 (finiteEntropy (countMass counts) / factors)) := by
  have hpop := (tendsto_log_exactWords_card_mul counts hD).comp (tendsto_add_atTop_nat 1)
  have hnormalized := hpop.div_const (factors : ℝ)
  change Tendsto _ atTop (𝓝 (finiteEntropy (countMass counts) / factors)) at hnormalized
  apply hnormalized.congr
  intro n
  symm
  change Real.log ((rows H counts (n + 1) * inner H counts (n + 1) *
    columns H counts (n + 1) : ℕ) : ℝ) /
    ((factors * blocks counts (n + 1) : ℕ) : ℝ) = _
  rw [volume_eq_copies H counts (n + 1) complete]
  simp only [copies, blocks, CompletionExecution.realize_label_card H counts (n + 1) complete]
  exact normalize_log _ (n + 1) (∑ a, counts a) factors (Nat.succ_pos n) hD factors_pos

theorem score_limit (β : ℝ) :
    Tendsto (fun n =>
      (positiveRealization H counts hD complete source supported unit factors_pos n).rates.score β)
      atTop (𝓝 (β / (3 * factors) * finiteEntropy (countMass counts))) := by
  have hm := multiplicity_rate H counts hD complete source supported unit factors_pos
  have ha := auxiliary_rate H counts hD complete source supported unit factors_pos
  have hv := volume_rate H counts hD complete source supported unit factors_pos
  have hl := (hm.sub ha).add (hv.const_mul (β / 3))
  have he : finiteEntropy (countMass counts) / factors -
      finiteEntropy (countMass counts) / factors +
      β / 3 * (finiteEntropy (countMass counts) / factors) =
        β / (3 * factors) * finiteEntropy (countMass counts) := by ring
  rw [he] at hl
  apply hl.congr
  intro n
  simp only [FiniteConstructionRates.score, FiniteMMRealization.rates]
  ring

include H hD complete source supported unit factors_pos in
theorem omega_lt_of_entropy_gap (β : ℝ)
    (gap : Real.log 3 < β / (3 * factors) * finiteEntropy (countMass counts)) :
    MatrixMultiplication.Foundation.Arithmetic.omega < β :=
  ComplexWitness.omega_lt_of_score_limit
    (positiveRealization H counts hD complete source supported unit factors_pos)
    (score_limit H counts hD complete source supported unit factors_pos β) gap

end MatrixMultiplication.CompletionSquareRates

end

end OAI
