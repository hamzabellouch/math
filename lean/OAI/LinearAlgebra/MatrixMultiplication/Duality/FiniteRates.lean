import OAI.LinearAlgebra.MatrixMultiplication.Duality.FiniteRealization
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalRateBridge

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualFiniteRealization

open MatrixMultiplication.Foundation CompletionHierarchyWords CompletionExecution
open CompletionFiniteRealization StageHierarchyResources ConditionalLabels Filter
open scoped BigOperators Topology Classical

variable {A X Y Z : Type} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ)
variable (hD : 0 < ∑ a, counts a)
variable (complete : Function.Injective (labelRecordOf H.labels H.depth))
variable (p : FiniteLaw A)
variable (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))

def pairRate (pair : ReaderPair) : ℝ :=
  lawPairingRate p H.labels H.depth (fun n => H.pair n.val) pair

include hD complete mass in
omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem copies_limit :
    Tendsto (fun t : ℕ => Real.log (copies H counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (finiteEntropy p.mass)) := by
  have hmass : (fun a => (counts a : ℝ) / (∑ b, counts b : ℕ)) = p.mass :=
    (funext mass).symm
  simpa only [copies, realize_label_card H counts _ complete, hmass] using
    tendsto_log_exactWords_card_mul counts hD

include hD complete mass in
omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem auxiliary_limit :
    Tendsto (fun t : ℕ => Real.log ((realize H counts t).execution.rankBound : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (finiteEntropy p.mass)) := by
  have hmass : (fun a => (counts a : ℝ) / (∑ b, counts b : ℕ)) = p.mass :=
    (funext mass).symm
  simpa only [realize_rankBound, hmass] using
    tendsto_log_stageAuxiliaryBudget counts hD H.labels H.depth complete

include hD in
theorem source_rank_limit (R : ℕ) :
    Tendsto (fun t : ℕ =>
      Real.log ((R ^ CompletionFiniteRealization.blocks counts t : ℕ) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (Real.log R)) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  have htD : (t : ℝ) * (∑ a, counts a : ℕ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr ht) hD'
  rw [Nat.cast_pow, Real.log_pow, CompletionFiniteRealization.blocks, Nat.cast_mul]
  exact (mul_div_cancel_left₀ (Real.log R) htD).symm

include hD complete mass in
omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem rank_budget_limit {R : ℕ} (hR : 0 < R) :
    Tendsto (fun t : ℕ => Real.log (rankBudget H counts t R : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (Real.log R + finiteEntropy p.mass)) := by
  apply ((source_rank_limit counts hD R).add
    (auxiliary_limit H counts hD complete p mass)).congr
  intro t
  have hs : ((R ^ CompletionFiniteRealization.blocks counts t : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hR))
  have ha : ((realize H counts t).execution.rankBound : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (auxiliaryRank_pos H counts t))
  rw [rankBudget, Nat.cast_mul, Real.log_mul hs ha, add_div]

variable {T : Tensor ℂ X Y Z} {R d D : ℕ}
variable (source : Tensor.PolynomialApproximation T R d D) (hR : 0 < R)
variable (supported : ∀ x y z, T x y z ≠ 0 →
  ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)

include hD mass in
theorem witness_outer_limit :
    Tendsto (fun t : ℕ =>
      Real.log ((witness H counts t complete source hR supported unit).outer : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (pairRate H p .xy + pairRate H p .xz)) := by
  have hi := tendsto_log_stagePairingSize_law counts hD p mass H.labels H.depth
    (fun n => H.pair n.val) .xy
  have hr := tendsto_log_stagePairingSize_law counts hD p mass H.labels H.depth
    (fun n => H.pair n.val) .xz
  apply (hi.add hr).congr
  intro t
  rw [(witness_dimensions H counts t complete source hR supported unit).1,
    Nat.cast_mul, Real.log_mul]
  · ring
  · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (pairingSize_pos _ _ _ (fun n => stageRefinementCount_pos counts H.labels n.val t)))
  · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (pairingSize_pos _ _ _ (fun n => stageRefinementCount_pos counts H.labels n.val t)))

include hD mass in
theorem witness_inner_limit :
    Tendsto (fun t : ℕ =>
      Real.log ((witness H counts t complete source hR supported unit).inner : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (2 * pairRate H p .yz)) := by
  apply ((tendsto_log_stagePairingSize_law counts hD p mass H.labels H.depth
    (fun n => H.pair n.val) .yz).const_mul 2).congr
  intro t
  rw [(witness_dimensions H counts t complete source hR supported unit).2,
    Nat.cast_pow, Real.log_pow]
  norm_num
  ring

include hD mass in
theorem witness_multiplicity_limit :
    Tendsto (fun t : ℕ =>
      Real.log ((witness H counts t complete source hR supported unit).multiplicity : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (2 * finiteEntropy p.mass)) := by
  apply ((copies_limit H counts hD complete p mass).const_mul 2).congr
  intro t
  rw [witness_multiplicity, Nat.cast_pow, Real.log_pow]
  norm_num
  ring

include hD mass in
theorem witness_rank_limit :
    Tendsto (fun t : ℕ =>
      Real.log ((witness H counts t complete source hR supported unit).rank : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (2 * (Real.log R + finiteEntropy p.mass))) := by
  apply ((rank_budget_limit H counts hD complete p mass hR).const_mul 2).congr
  intro t
  rw [witness_rank, Nat.cast_pow, Real.log_pow]
  simp only [rankBudget, Nat.cast_mul, Nat.cast_pow]
  norm_num
  ring

end MatrixMultiplication.DualFiniteRealization

end

end OAI
