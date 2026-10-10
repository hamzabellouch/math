import OAI.NumberTheory.CubicMoment.Estimates.SparseStoppingLabels
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleCount

namespace OAI

/-! Explicit logarithmic aggregation costs for the actual finite stopping
labels on a fixed dilation of X. The inverse-binomial scalar is retained,
and the bounds apply to every early or late subset of labels. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stoppingLabelBox_card_fixed {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : ℝ, 1 ≤ F →
      ((stoppingLabelBox ρ F).card:ℝ) ≤ K*(1+Real.log F)^3 := by
  obtain ⟨C,hC,hbin⟩ := geometricBinCount_log_bound hρ
  let D : ℝ := (Real.log 2)⁻¹+2
  have hlog2 : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C*D^2,by positivity,?_⟩
  intro F hF
  have hL := Real.log_nonneg hF
  have hf := stoppingFactorLimit_bound hF
  have hfac : ((stoppingFactorLimit F+1:ℕ):ℝ) ≤ D*(1+Real.log F) := by
    simp only [Nat.cast_add,Nat.cast_one]
    dsimp [D]
    nlinarith
  have hcard : ((stoppingLabelBox ρ F).card:ℝ) ≤
      (geometricBinCount ρ F:ℝ)*((stoppingFactorLimit F+1:ℕ):ℝ)^2 := by
    exact_mod_cast stoppingLabelBox_card ρ F
  calc
    _ ≤ (C*(1+Real.log F))*(D*(1+Real.log F))^2 :=
      hcard.trans (mul_le_mul (hbin F hF)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hfac 2) (sq_nonneg _) (by positivity))
    _ = (C*D^2)*(1+Real.log F)^3 := by ring

theorem stoppingLabelBox_card_dilated {ρ c : ℝ} (hρ : 1 < ρ) (hc : 1 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      ((stoppingLabelBox ρ (c*X)).card:ℝ) ≤ K*(1+Real.log X)^3 := by
  obtain ⟨C,hC,hbound⟩ := stoppingLabelBox_card_fixed hρ
  have hclog := Real.log_nonneg hc
  have hcp : 0 < c := zero_lt_one.trans_le hc
  refine ⟨C*(1+Real.log c)^3,by positivity,?_⟩
  intro X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlogX := Real.log_nonneg hX
  have hF : 1 ≤ c*X := one_le_mul_of_one_le_of_one_le hc hX
  have hL : 1+Real.log (c*X) ≤ (1+Real.log c)*(1+Real.log X) := by
    rw [Real.log_mul hcp.ne' hXp.ne']
    nlinarith [mul_nonneg hclog hlogX]
  calc
    _ ≤ C*(1+Real.log (c*X))^3 := hbound _ hF
    _ ≤ C*((1+Real.log c)*(1+Real.log X))^3 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity [Real.log_nonneg hF]) hL 3) hC.le
    _ = (C*(1+Real.log c)^3)*(1+Real.log X)^3 := by ring

/-- One constant covers arbitrary early/late label subsets and every
family of piece bounds. In particular, no sign is discarded from a piece. -/
theorem stopping_label_weighted_sum_dilated {ρ c : ℝ} (hρ : 1 < ρ) (hc : 1 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ I : Finset (ℕ × ℕ × ℕ), I ⊆ stoppingLabelBox ρ (c*X) →
      (I.card:ℝ) ≤ K*(1+Real.log X)^3 ∧
      ∀ (f : (ℕ × ℕ × ℕ) → ℂ) (M : ℝ), 0 ≤ M →
        (∀ q ∈ I, ‖f q‖ ≤ M) →
        ‖∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*f q‖ ≤
          K*(1+Real.log X)^3*M := by
  obtain ⟨K,hK,hcount⟩ := stoppingLabelBox_card_dilated hρ hc
  refine ⟨K,hK,?_⟩
  intro X hX I hI
  have hcard : (I.card:ℝ) ≤ K*(1+Real.log X)^3 :=
    (Nat.cast_le.mpr (Finset.card_le_card hI)).trans (hcount X hX)
  refine ⟨hcard,?_⟩
  intro f M hM hf
  calc
    _ ≤ ∑ q ∈ I, ‖(Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*f q‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ I, M := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_mul (stopping_scalar_norm_le_one q.2.1 q.2.2) (hf q hq)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    _ = (I.card:ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hM

lemma stopping_early_labels_subset (ρ F : ℝ) (h : ℕ) :
    (stoppingLabelBox ρ F).filter (fun q => q.1 < h) ⊆ stoppingLabelBox ρ F :=
  Finset.filter_subset _ _

/-- The low distinguished-scale restriction can only lower the number of
norm-partition indices; its exact cutoff need not be relaxed. -/
theorem stopped_norm_partition_subset_count (i : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ I : Finset (Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
        (I.card:ℝ) ≤ D*(1+Real.log X)^i := by
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i 0
  refine ⟨D,hD,?_⟩
  intro X hX I
  have hi : (I.card:ℝ) ≤ (Fintype.card
      (Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))):ℝ) := by
    exact_mod_cast Finset.card_le_univ I
  apply hi.trans
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,Nat.add_zero,Nat.cast_pow]
    using hcount X hX

end CubicFirstMoment

end

end OAI
