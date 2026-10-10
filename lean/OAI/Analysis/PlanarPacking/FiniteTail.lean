import OAI.Analysis.PlanarPacking.FiniteProjection
import OAI.Analysis.PlanarPacking.CanonicalRows
import OAI.Analysis.PlanarPacking.Certificate.LEntries

namespace OAI

/-!
# Tails of the interpolation operator

Coordinate projections and shell estimates bound the tails of the interpolation operator.
-/

namespace SharpPlanar
open scoped BigOperators
noncomputable def tailScalar (x : X) (N : ℕ) : ℝ :=
  ∑' k : Node × Bool, if N<k.1.val then |x k| else 0
lemma tailScalar_summable (x : X) (N : ℕ) :
    Summable (fun k : Node × Bool => if N<k.1.val then |x k| else 0) := by
  apply Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) _ (X_summable x)
  intro k
  split_ifs <;> simp [abs_nonneg]
lemma tailScalar_eq (x : X) (N : ℕ) : tailScalar x N = rowTailNorm x N := by
  unfold tailScalar rowTailNorm
  rw [(tailScalar_summable x N).tsum_prod]
  change _ = ∑' n : {n : Node // n ∈ {n : Node | N<n.val}}, (fun n : Node => |x (n,false)|+|x (n,true)|) n.val
  rw [tsum_subtype {n : Node | N<n.val} (fun n : Node => |x (n,false)|+|x (n,true)|)]
  apply tsum_congr
  intro n
  simp only [tsum_fintype, Fintype.sum_bool, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp [add_comm]
lemma rowTailNorm_nonneg (x : X) (N : ℕ) : 0 ≤ rowTailNorm x N :=
  tsum_nonneg (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
lemma rowTailNorm_zero (x : X) : rowTailNorm x 0 = ‖x‖ := by
  rw [← tailScalar_eq,X_norm_scalar]
  apply tsum_congr
  intro k
  exact ite_eq_left k.1.prop.1
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_tail (N : ℕ) (hN : ∀ i, N<(e i).1.val) (x : X) :
    ‖finiteRestriction e he x‖ ≤ rowTailNorm x N := by
  rw [l1Finite_norm,← tailScalar_eq]
  have hh := tsum_comp_le_tsum_of_inj (tailScalar_summable x N)
    (fun k => by split_ifs <;> positivity) he
  simpa only [Function.comp_apply, hN, ite_true, tsum_fintype,finiteRestriction_apply,tailScalar] using hh
end
lemma norm_S_le : ‖S‖ ≤ 28 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [← rowTailNorm_zero (S x)]
  exact (sharp_S_tail x 0).trans (mul_le_mul_of_nonneg_right rowTable_bounds.1.le (norm_nonneg _))
end SharpPlanar
namespace SharpPlanar.Numerical
open scoped BigOperators
lemma exterior_low_tail (x : X) : ‖RE x‖ ≤ ‖RL x‖ + rowTailNorm x 16 := by
  have hh := tsum_comp_le_tsum_of_inj (tailScalar_summable x 16)
    (fun k => by split_ifs <;> positivity) exteriorIndex_injective
  have hh' : (∑ i, if 16<(exteriorIndex i).1.val then |x (exteriorIndex i)| else 0)
      ≤ rowTailNorm x 16 := by
    rw [← tailScalar_eq]
    simpa only [Function.comp_apply,tsum_fintype,tailScalar] using hh
  have hi : ‖RE (IL (RL x))‖ ≤ ‖RL x‖ := by
    exact (finiteRestriction_bound _ exteriorIndex_injective _).trans_eq (by rw [one_mul,finiteEmbedding_norm _ lowExteriorIndex_injective])
  calc
    ‖RE x‖ ≤ ‖RE (IL (RL x))‖ +
        ∑ i, if 16<(exteriorIndex i).1.val then |x (exteriorIndex i)| else 0 := by
      rw [l1Finite_norm,l1Finite_norm,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      simp only [finiteRestriction_apply]
      rw [finiteProjection_apply]
      by_cases h : 16<(exteriorIndex i).1.val
      · simp only [h,ite_true]
        exact le_add_of_nonneg_left (abs_nonneg _)
      · have hmem : ∃ j, lowExteriorIndex j=exteriorIndex i :=
          (lowExteriorIndex_range (exteriorIndex i).1 (exteriorIndex i).2).mpr
            ⟨(exteriorIndex_bound i).1, Nat.le_of_not_gt h⟩
        rw [ite_eq_left hmem,ite_eq_right h,add_zero]
    _ ≤ ‖RL x‖ + rowTailNorm x 16 := add_le_add hi hh'
lemma compressed_low_L : RL.comp (S.comp IJ) = matrixL1 Lmat := by
  rw [compressed_S_matrix]
  rfl
lemma exterior_central_norm : ‖RE.comp (S.comp IJ)‖ ≤ (11:ℝ)/100 := by
  have hlow : ‖RL.comp (S.comp IJ)‖ ≤ (88:ℝ)/1000 := by
    rw [compressed_low_L]
    exact (matrixL1_norm_lt Lmat_column).le
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have h := exterior_low_tail (S (IJ x))
  have hL : ‖RL (S (IJ x))‖ ≤ (88:ℝ)/1000 * ‖x‖ :=
    ((RL.comp (S.comp IJ)).le_opNorm x).trans (mul_le_mul_of_nonneg_right hlow (norm_nonneg _))
  have ht := sharp_S_tail (IJ x) 16
  rw [finiteEmbedding_norm _ centralIndex_injective] at ht
  have ht' := mul_le_mul_of_nonneg_right rowTable_bounds.2.2.1.le (norm_nonneg x)
  change ‖RE (S (IJ x))‖ ≤ _
  nlinarith [norm_nonneg x]
lemma exterior_exterior_norm : ‖RE.comp (S.comp IE)‖ ≤ (28:ℝ)/100 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have h := finiteRestriction_tail exteriorIndex exteriorIndex_injective 4
    (fun i => (exteriorIndex_bound i).1) (S (IE x))
  have ht := sharp_S_tail (IE x) 4
  rw [finiteEmbedding_norm _ exteriorIndex_injective] at ht
  exact h.trans (ht.trans (mul_le_mul_of_nonneg_right rowTable_bounds.2.1.le (norm_nonneg _)))
lemma finite_discard_norm (x : X) : ‖x - IF (RF x)‖ = rowTailNorm x 100 := by
  rw [X_norm_scalar,← tailScalar_eq]
  apply tsum_congr
  intro k
  change |x k - IF (RF x) k| = _
  rw [finiteProjection_apply]
  simp only [finiteIndex_range]
  by_cases h : k.1.val ≤ 100
  · simp [h, Nat.not_lt_of_ge h]
  · simp [h, Nat.lt_of_not_ge h]
lemma finite_discard_S (x : X) : ‖S x - IF (RF (S x))‖ ≤ (1:ℝ)/2000000000 * ‖x‖ := by
  rw [finite_discard_norm]
  exact (sharp_S_tail x 100).trans (mul_le_mul_of_nonneg_right (by
    convert rowTable_bounds.2.2.2.le using 1
    norm_num) (norm_nonneg _))
end SharpPlanar.Numerical

end OAI
