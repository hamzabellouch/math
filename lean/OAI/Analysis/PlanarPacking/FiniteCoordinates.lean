import OAI.Analysis.PlanarPacking.Cardinal
import OAI.Analysis.PlanarPacking.MatrixL1

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
lemma X_norm_scalar (x : X) : ‖x‖ = ∑' i : Node × Bool, |x i| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one,Real.rpow_one,one_div_one,Real.norm_eq_abs]
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
noncomputable def finiteRestrictionLinear : X →ₗ[ℝ] L1Finite ι where
  toFun x := WithLp.toLp 1 (fun i => x (e i))
  map_add' := by intro x y; ext i; rfl
  map_smul' := by intro r x; ext i; rfl
include he in
lemma finiteRestriction_bound (x : X) : ‖finiteRestrictionLinear e x‖ ≤ 1*‖x‖ := by
  rw [l1Finite_norm,X_norm_scalar,one_mul]
  change (∑ i, |x (e i)|) ≤ _
  simpa only [tsum_fintype, Function.comp_apply] using tsum_comp_le_tsum_of_inj (X_summable x) (fun _ => abs_nonneg _) he
noncomputable def finiteRestriction : X →L[ℝ] L1Finite ι :=
  (finiteRestrictionLinear e).mkContinuous 1 (finiteRestriction_bound e he)
lemma finiteRestriction_apply (x : X) (i : ι) : finiteRestriction e he x i = x (e i) := rfl
noncomputable def finiteEmbeddingLinear : L1Finite ι →ₗ[ℝ] X where
  toFun x := ∑ i, lp.single 1 (e i) (x i)
  map_add' := by intro x y; simp only [PiLp.add_apply,lp.single_add,Finset.sum_add_distrib]
  map_smul' := by intro r x; simp only [PiLp.smul_apply,lp.single_smul,Finset.smul_sum]; rfl
lemma finiteEmbedding_bound (x : L1Finite ι) : ‖finiteEmbeddingLinear e x‖ ≤ 1*‖x‖ := by
  rw [one_mul,l1Finite_norm]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by simp [lp.norm_single]))
noncomputable def finiteEmbedding : L1Finite ι →L[ℝ] X :=
  (finiteEmbeddingLinear e).mkContinuous 1 (finiteEmbedding_bound e)
lemma finiteEmbedding_apply (x : L1Finite ι) (i : Node × Bool) :
    finiteEmbedding e x i = ∑ j, if e j=i then x j else 0 := by
  change (∑ j, lp.single 1 (e j) (x j) : X) i = _
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply, eq_comm]
lemma finiteRestriction_embedding (x : L1Finite ι) :
    finiteRestriction e he (finiteEmbedding e x) = x := by
  classical
  ext i
  rw [finiteRestriction_apply,finiteEmbedding_apply]
  simp only [he.eq_iff]
  simp
include he in
lemma finiteEmbedding_norm (x : L1Finite ι) : ‖finiteEmbedding e x‖ = ‖x‖ := by
  apply le_antisymm
  · exact (finiteEmbedding_bound e x).trans_eq (one_mul _)
  · have hh := finiteRestriction_bound e he (finiteEmbedding e x)
    change ‖finiteRestriction e he (finiteEmbedding e x)‖ ≤ _ at hh
    simpa only [finiteRestriction_embedding,one_mul] using hh
lemma finiteRestriction_norm : ‖finiteRestriction e he‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (finiteRestriction_bound e he)
lemma finiteEmbedding_norm_le : ‖finiteEmbedding e‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (finiteEmbedding_bound e)
end
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  (e : ι → Node × Bool) (he : Function.Injective e)
  (f : κ → Node × Bool)
lemma compressed_S_matrix :
    (finiteRestriction e he).comp (S.comp (finiteEmbedding f)) =
      matrixL1 (fun i j => S (lp.single 1 (f j) 1) (e i)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,finiteRestriction_apply]
  change S (∑ j, lp.single 1 (f j) (x j)) (e i) = _
  rw [map_sum]
  simp only [lp.coeFn_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (lp.single 1 (f j) (x j) : X) = (x j) • (lp.single 1 (f j) 1 : X) := by
    rw [← lp.single_smul]; simp
  rw [hs,map_smul]
  change x j * S (lp.single 1 (f j) 1) (e i) = S (lp.single 1 (f j) 1) (e i) * x j
  ring
end
end SharpPlanar

end OAI
