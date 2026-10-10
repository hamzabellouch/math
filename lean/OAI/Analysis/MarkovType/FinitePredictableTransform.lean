import OAI.Analysis.MarkovType.FiniteMartingaleBasic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def partialSumProcess (d : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  ∑ j ∈ Finset.range n, d (j + 1) ω

omit sectionFintypeΩ sectionNormedSpaceℝE in
@[simp] theorem partialSumProcess_zero [Fintype Ω] [NormedSpace ℝ E] (d : ℕ → Ω → E) (ω : Ω) :
    partialSumProcess d 0 ω = 0 := by
  simp [partialSumProcess]

@[simp] theorem difference_partialSumProcess_succ (d : ℕ → Ω → E)
    (n : ℕ) (ω : Ω) :
    finiteDifference (partialSumProcess d) (n + 1) ω = d (n + 1) ω := by
  simp only [finiteDifference_succ, partialSumProcess, Finset.sum_range_succ]
  abel

theorem partialSumProcess_isMartingale (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (d : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j)) :
    F.IsMartingaleUpTo μ (partialSumProcess d) N := by
  constructor
  · intro n hn ω η hωη
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    exact hadapt (j + 1) (Nat.succ_pos j) (hjn.trans hn) (F.refines hjn hωη)
  · intro j hj hjN
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    have hd : finiteDifference (partialSumProcess d) (n + 1) = d (n + 1) :=
      funext (difference_partialSumProcess_succ d n)
    rw [hd]
    exact hzero (n + 1) (Nat.succ_pos n) hjN

theorem predictableTransform_isMartingale (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (d : ℕ → Ω → E) (c : ℕ → Ω → ℝ) (N : ℕ)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j))
    (hc : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (c j)) :
    F.IsMartingaleUpTo μ (partialSumProcess (fun j ω => c j ω • d j ω)) N := by
  apply partialSumProcess_isMartingale F μ _ N
  · intro j hj hjN ω η hωη
    dsimp only
    rw [hc j hj hjN (F.refines (Nat.sub_le j 1) hωη),
      hadapt j hj hjN hωη]
  · intro j hj hjN
    exact (hzero j hj hjN).predictable_smul (c j) (hc j hj hjN)

def cumulativeCost (w : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, w (j + 1) ω

omit sectionFintypeΩ in
@[simp] theorem cumulativeCost_zero [Fintype Ω] (w : ℕ → Ω → ℝ) (ω : Ω) :
    cumulativeCost w 0 ω = 0 := by simp [cumulativeCost]

omit sectionFintypeΩ in
theorem cumulativeCost_succ [Fintype Ω] (w : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cumulativeCost w (n + 1) ω = cumulativeCost w n ω + w (n + 1) ω := by
  exact Finset.sum_range_succ _ _

theorem cumulativeCost_mono (w : ℕ → Ω → ℝ)
    (hw : ∀ j ω, 0 ≤ w j ω) (ω : Ω) :
    Monotone (fun n => cumulativeCost w n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [cumulativeCost_succ]
  exact le_add_of_nonneg_right (hw (n + 1) ω)

omit sectionFintypeΩ in
theorem cumulativeCost_predictable [Fintype Ω] (F : FinitePartitionFiltration Ω)
    (w : ℕ → Ω → ℝ) (N : ℕ)
    (hw : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (w j))
    {n : ℕ} (hn : n ≤ N) :
    F.AdaptedAt (n - 1) (cumulativeCost w n) := by
  intro ω η hωη
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  have hpart : j + 1 - 1 ≤ n - 1 := Nat.sub_le_sub_right hjn 1
  exact hw (j + 1) (Nat.succ_pos j) (hjn.trans hn) (F.refines hpart hωη)

def budgetCoefficient (w : ℕ → Ω → ℝ) (S : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  if cumulativeCost w j ω ≤ S then 1 else 0

theorem budgetCoefficient_predictable (F : FinitePartitionFiltration Ω)
    (w : ℕ → Ω → ℝ) (N : ℕ) (S : ℝ)
    (hw : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (w j))
    {n : ℕ} (hn : n ≤ N) :
    F.AdaptedAt (n - 1) (budgetCoefficient w S n) := by
  intro ω η hωη
  unfold budgetCoefficient
  rw [cumulativeCost_predictable F w N hw hn hωη]

theorem budgetTransform_isMartingale (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (d : ℕ → Ω → E) (w : ℕ → Ω → ℝ) (N : ℕ) (S : ℝ)
    (hadapt : ∀ j, 0 < j → j ≤ N → F.AdaptedAt j (d j))
    (hzero : ∀ j, 0 < j → j ≤ N →
      HasZeroConditionalSum μ (F.part (j - 1)) (d j))
    (hw : ∀ j, 0 < j → j ≤ N → F.AdaptedAt (j - 1) (w j)) :
    F.IsMartingaleUpTo μ
      (partialSumProcess (fun j ω => budgetCoefficient w S j ω • d j ω)) N := by
  apply predictableTransform_isMartingale F μ d (budgetCoefficient w S) N hadapt hzero
  intro j hj hjN
  exact budgetCoefficient_predictable F w N S hw hjN

theorem budgetCoefficient_eq_one_of_cost_le (w : ℕ → Ω → ℝ)
    (hw : ∀ j ω, 0 ≤ w j ω) {S : ℝ} {n j : ℕ} {ω : Ω}
    (hj : j ≤ n) (hcost : cumulativeCost w n ω ≤ S) :
    budgetCoefficient w S j ω = 1 := by
  apply ite_eq_left
  exact (cumulativeCost_mono w hw ω hj).trans hcost

theorem budgetTransform_eq_of_cost_le (d : ℕ → Ω → E) (w : ℕ → Ω → ℝ)
    (hw : ∀ j ω, 0 ≤ w j ω) {S : ℝ} {N n : ℕ} {ω : Ω}
    (hn : n ≤ N) (hcost : cumulativeCost w N ω ≤ S) :
    partialSumProcess (fun j η => budgetCoefficient w S j η • d j η) n ω =
      partialSumProcess d n ω := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j + 1 ≤ N := (Nat.succ_le_of_lt (Finset.mem_range.mp hj)).trans hn
  dsimp only
  rw [budgetCoefficient_eq_one_of_cost_le w hw hjN hcost, one_smul]

theorem retainedCost_eq_of_cost_le (w : ℕ → Ω → ℝ)
    (hw : ∀ j ω, 0 ≤ w j ω) {S : ℝ} {n : ℕ} {ω : Ω}
    (hcost : cumulativeCost w n ω ≤ S) :
    cumulativeCost (fun j η => budgetCoefficient w S j η * w j η) n ω =
      cumulativeCost w n ω := by
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [budgetCoefficient_eq_one_of_cost_le w hw
    (Nat.succ_le_of_lt (Finset.mem_range.mp hj)) hcost, one_mul]

theorem retainedCost_le (w : ℕ → Ω → ℝ) (hw : ∀ j ω, 0 ≤ w j ω)
    {S : ℝ} (hS : 0 ≤ S) (n : ℕ) (ω : Ω) :
    cumulativeCost (fun j η => budgetCoefficient w S j η * w j η) n ω ≤ S := by
  induction n with
  | zero => simpa only [cumulativeCost_zero] using hS
  | succ n ih =>
    by_cases hcost : cumulativeCost w (n + 1) ω ≤ S
    · rw [retainedCost_eq_of_cost_le w hw hcost]
      exact hcost
    · rw [cumulativeCost_succ]
      simp only [budgetCoefficient, ite_eq_right hcost, zero_mul, add_zero]
      exact ih

theorem budgetTransform_energy_le (d : ℕ → Ω → E) {p S : ℝ}
    (hp : 0 < p) (hS : 0 ≤ S) (n : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range n,
      ‖budgetCoefficient (fun k η => ‖d k η‖ ^ p) S (j + 1) ω • d (j + 1) ω‖ ^ p)
      ≤ S := by
  have heq : (∑ j ∈ Finset.range n,
      ‖budgetCoefficient (fun k η => ‖d k η‖ ^ p) S (j + 1) ω • d (j + 1) ω‖ ^ p) =
      cumulativeCost (fun j η =>
        budgetCoefficient (fun k ξ => ‖d k ξ‖ ^ p) S j η * ‖d j η‖ ^ p) n ω := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    unfold budgetCoefficient
    split_ifs with h <;> simp [ Real.zero_rpow (ne_of_gt hp)]
  rw [heq]
  exact retainedCost_le (fun j η => ‖d j η‖ ^ p)
    (fun j η => Real.rpow_nonneg (norm_nonneg _) _) hS n ω

end MarkovSuperreflexivity

end

end OAI
