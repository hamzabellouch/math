import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.DenseCanonicalParser
import OAI.Analysis.MatrixSigning.Optimization.Coordinates
import OAI.Analysis.MatrixSigning.Realization.FaceQueryRealization
import OAI.Combinatorics.ThinTrees.Representation

namespace OAI

/-! Normalization descent. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

section Covariance
variable {E I : Type*} [normalizationFintypeE : Fintype E]
  [normalizationDecidableEqE : DecidableEq E] [normalizationFintypeI : Fintype I]
  [normalizationDecidableEqI : DecidableEq I]

def covariance {K : Type*} [Field K] (v : E → I → K) (a : E → K) : Matrix I I K :=
  ∑e, a e • vecMulVec (v e) (v e)

noncomputable def leverage (v : E → I → ℝ) (a : E → ℝ) (e : E) : ℝ :=
  a e * (v e ⬝ᵥ ((covariance v a)⁻¹ *ᵥ v e))

noncomputable def objective (q : ℕ) (v : E → I → ℝ) (a : E → ℝ) : ℝ :=
  Real.log (covariance v a).det-(∑e, Real.log (a e))/q

def shrink {K : Type*} [Field K] (δ : K) (a : E → K) (e : E) : E → K :=
  Function.update a e ((1-δ)*a e)

omit normalizationFintypeE in
lemma shrink_pos [_shrinkFintypeE : Fintype E] {δ : ℝ} (hδ : δ < 1)
    {a : E → ℝ} (ha : ∀e, 0 < a e) (e : E) :
    ∀f, 0 < shrink δ a e f := by
  intro f
  by_cases h : f=e
  · subst f
    simpa [shrink] using mul_pos (sub_pos.mpr hδ) (ha e)
  · simpa only [shrink,Function.update_of_ne h] using ha f

omit normalizationFintypeI normalizationDecidableEqI in
lemma covariance_shrink [_covarianceShrinkFintypeI : Fintype I]
    [_covarianceShrinkDecidableEqI : DecidableEq I] {K : Type*} [Field K] (v : E → I → K)
    (a : E → K) (e : E) (δ : K) :
    covariance v (shrink δ a e) = covariance v a - (δ*a e) • vecMulVec (v e) (v e) := by
  classical
  have h : (fun f => shrink δ a e f • vecMulVec (v f) (v f)) =
      Function.update (fun f => a f • vecMulVec (v f) (v f)) e
        (((1-δ)*a e) • vecMulVec (v e) (v e)) := by
    funext f
    by_cases he : f=e
    · subst f; simp [shrink]
    · simp only [shrink,Function.update_of_ne he]
  unfold covariance
  rw [h,Finset.sum_update_of_mem (mem_univ e),sdiff_singleton_eq_erase]
  rw [←Finset.add_sum_erase univ (fun f => a f • vecMulVec (v f) (v f)) (mem_univ e)]
  module

lemma log_shrink_sum {δ : ℝ} (hδ : δ < 1) {a : E → ℝ} (ha : ∀e, 0 < a e) (e : E) :
    (∑f, Real.log (shrink δ a e f)) = (∑f, Real.log (a f))+Real.log (1-δ) := by
  have h : (fun f => Real.log (shrink δ a e f)) =
      Function.update (fun f => Real.log (a f)) e (Real.log ((1-δ)*a e)) := by
    funext f
    by_cases he : f=e
    · subst f; simp [shrink]
    · simp only [shrink,Function.update_of_ne he]
  rw [h,Finset.sum_update_of_mem (mem_univ e),sdiff_singleton_eq_erase,
    Real.log_mul (sub_pos.mpr hδ).ne' (ha e).ne']
  rw [←Finset.add_sum_erase univ (fun f => Real.log (a f)) (mem_univ e)]
  ring

lemma det_rank_one (A : Matrix I I ℝ) (hA : A.PosDef) (v : I → ℝ) (c : ℝ) :
    (A+c • vecMulVec v v).det=A.det*(1+c*(v ⬝ᵥ (A⁻¹ *ᵥ v))) := by
  have he : (Matrix.replicateCol Unit (c • v) * Matrix.replicateRow Unit v)=c • vecMulVec v v := by
    ext i j
    simp [Matrix.mul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
    ring
  rw [←he,Matrix.det_add_replicateCol_mul_replicateRow
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.det_unique (n := Unit)]
  congr 1
  simp only [Matrix.add_apply,Matrix.one_apply_eq]
  change 1+(v ᵥ* A⁻¹) ⬝ᵥ (c • v) = 1+c*(v ⬝ᵥ (A⁻¹ *ᵥ v))
  rw [dotProduct_smul,←Matrix.dotProduct_mulVec,smul_eq_mul]

lemma det_shrink (v : E → I → ℝ) (a : E → ℝ) (e : E) (δ : ℝ)
    (hA : (covariance v a).PosDef) :
    (covariance v (shrink δ a e)).det=(covariance v a).det*(1-δ*leverage v a e) := by
  rw [covariance_shrink,sub_eq_add_neg,←neg_smul,
    det_rank_one _ hA (v e) (-(δ*a e)),leverage]
  ring

omit normalizationDecidableEqE in
lemma leverage_test [_leverageTestDecidableEqE : DecidableEq E]
    (v : E → I → ℝ) (a : E → ℝ) (e : E)
    (hA : (covariance v a).PosDef) (ha : 0 < a e) {t : ℝ} (ht : 0 < t) :
    leverage v a e ≤ t ↔ (t • covariance v a - a e • vecMulVec (v e) (v e)).PosSemidef := by
  have h := resistance_order hA (Real.sqrt (a e) • v e) ht
  have hs : Real.sqrt (a e)*Real.sqrt (a e)=a e := Real.mul_self_sqrt ha.le
  simpa only [leverage,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    ←mul_assoc,hs,Matrix.smul_vecMulVec,Matrix.vecMulVec_smul,smul_smul] using h

lemma neg_log_one_sub {δ : ℝ} (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    -Real.log (1-δ) ≤ δ+2*δ^2 := by
  have hp : 0 < 1-δ := by linarith only [hδ1]
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hh
  have hfrac : (1-δ)⁻¹-1 ≤ δ+2*δ^2 := by
    rw [inv_eq_one_div,div_sub_one hp.ne',div_le_iff₀ hp]
    nlinarith [sq_nonneg δ,mul_nonneg (sq_nonneg δ) (show 0 ≤ 1-2*δ by linarith)]
  exact hh.trans hfrac

lemma objective_drop (q : ℕ) (hq : 1 ≤ q) (v : E → I → ℝ)
    (a : E → ℝ) (ha : ∀e, 0 < a e) (e : E) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hA : (covariance v a).PosDef) (hA' : (covariance v (shrink δ a e)).PosDef)
    (he : 1/(q:ℝ)+4*δ < leverage v a e) :
    objective q v (shrink δ a e) ≤ objective q v a-δ^2 := by
  have hδlt : δ < 1 := by linarith only [hδ1]
  have hd := det_shrink v a e δ hA
  have hp : 0 < 1-δ*leverage v a e := by
    have hh := hA'.det_pos
    rw [hd] at hh
    exact (mul_pos_iff_of_pos_left hA.det_pos).mp hh
  have hlog := Real.log_le_sub_one_of_pos hp
  have hneg := neg_log_one_sub hδ.le hδ1
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith only [hqR]
  have hqinv : 1/(q:ℝ) ≤ 1 := (div_le_one hq0).mpr hqR
  have hobj : objective q v (shrink δ a e) = objective q v a+
      Real.log (1-δ*leverage v a e)-Real.log (1-δ)/q := by
    unfold objective
    rw [hd,Real.log_mul hA.det_pos.ne' hp.ne',log_shrink_sum hδlt ha e]
    ring
  rw [hobj]
  have hmain := mul_lt_mul_of_pos_left he hδ
  have hdiv := div_le_div_of_nonneg_right hneg hq0.le
  have hrem : (δ+2*δ^2)/(q:ℝ) ≤ δ/q+2*δ^2 := by
    rw [add_div]
    apply add_le_add_right
    exact (div_le_self (by positivity) hqR)
  have hcancel : δ*(1/(q:ℝ))=δ/q := by ring
  rw [neg_div] at hdiv
  rw [mul_add,hcancel] at hmain
  nlinarith only [hmain,hlog,hdiv,hrem,sq_nonneg δ]

lemma logdet_le_trace {A : Matrix I I ℝ} (hA : A.PosDef) : Real.log A.det ≤ A.trace := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues,hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]
  apply sum_le_sum
  intro i _
  exact (Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)).trans (by linarith)

end Covariance

section Bases
variable {E : Type*} [Fintype E] [basisPackingDecidableEqE : DecidableEq E] {q d : ℕ}

structure BasisPacking (v : E → Fin d → ℝ) (q : ℕ) where
  positive : 0 < q
  edges : (Fin q × Fin d) ≃ E
  invertible : ∀t, IsUnit (Matrix.of (fun i j => v (edges (t,j)) i))
  determinant : ∀t, 1 ≤ (Matrix.det (fun i j => v (edges (t,j)) i))^2

namespace BasisPacking
variable {v : E → Fin d → ℝ} (B : BasisPacking v q)
noncomputable def matrices (t : Fin q) : Matrix (Fin d) (Fin d) ℝ := fun i j => v (B.edges (t,j)) i
noncomputable def logWeights (a : E → ℝ) : EuclideanSpace ℝ (Fin q × Fin d) :=
  WithLp.toLp 2 (fun e => Real.log (a (B.edges e)))

omit basisPackingDecidableEqE in
lemma covariance_eq [_covarianceEqDecidableEqE : DecidableEq E]
    (a : E → ℝ) (ha : ∀e, 0 < a e) :
    covariance v a=packingCov B.matrices (B.logWeights a) := by
  rw [packingCov_eq_sum,covariance,←B.edges.sum_comp]
  apply sum_congr rfl
  intro e _
  simp only [logWeights,PiLp.toLp_apply,Real.exp_log (ha _),matrices]

include B

lemma covariance_posDef (a : E → ℝ) (ha : ∀e, 0 < a e) : (covariance v a).PosDef := by
  have : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp B.positive
  rw [B.covariance_eq a ha]
  exact packingCov_posDef B.matrices B.invertible _

lemma objective_nonneg (a : E → ℝ) (ha : ∀e, 0 < a e) : 0 ≤ objective q v a := by
  have : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp B.positive
  have hn : ∀t, 0 ≤ Real.log ((B.matrices t).det^2) :=
    fun t => Real.log_nonneg (B.determinant t)
  have hb := packingObjective_bddBelow B.matrices B.invertible (B.logWeights a)
  have h0 : 0 ≤ (∑t, Real.log ((B.matrices t).det^2))/(Fintype.card (Fin q):ℝ) :=
    div_nonneg (sum_nonneg (fun t _ => hn t)) (Nat.cast_nonneg _)
  apply (h0.trans hb).trans_eq
  unfold packingObjective objective
  rw [←B.covariance_eq a ha,Fintype.card_fin]
  congr 2
  exact B.edges.sum_comp (fun e => Real.log (a e))

lemma initial_gap (hsize : ∀e, v e ⬝ᵥ v e ≤ 2) :
    objective q v (fun _ => 1) ≤ 2*Fintype.card E := by
  have hh := logdet_le_trace (B.covariance_posDef (fun _ => 1) (by simp))
  simp only [objective,Real.log_one,sum_const_zero,zero_div,sub_zero]
  apply hh.trans
  simp only [covariance,one_smul,Matrix.trace_sum,Matrix.trace_vecMulVec]
  calc
    _ ≤ ∑_e : E, (2:ℝ) := sum_le_sum (fun e _ => hsize e)
    _ = _ := by simp [mul_comm]

end BasisPacking
end Bases
end AlgorithmicThinTrees.Normalization
end

end OAI
