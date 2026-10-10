import OAI.Analysis.Triangular.Construction.ConcreteSchur
import OAI.Analysis.Triangular.Certificate.ParamActual
import OAI.Analysis.Triangular.Certificate.TargetInterval
import OAI.Analysis.Triangular.Certificate.ParamNorm

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

def finiteResidual (z : ℝ) : FiniteCoefficients :=
  column (fun i (_ : Unit) => if i.val<8 then 0 else
    gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩)
    (fun _ => (hasSum_fintype _).summable) ()
lemma finiteResidual_norm {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖finiteResidual z‖ ≤ finiteResidualBound := by
  rw [l1_norm,tsum_fintype]
  change (∑ i : Fin 20, |if i.val<8 then 0 else
    gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩|) ≤ _
  have he : (∑ i : Fin 20, |if i.val<8 then 0 else
      gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩|) =
      ∑ n : Fin 10, if n.val<4 then 0 else ∑ d : Fin 2, |gaussianTarget H z (finiteNode n) d| := by
    rw [show (fun i : Fin 20 => |if i.val<8 then 0 else
      gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩|) =
      (fun i : Fin 20 => (fun n : Fin 10 => fun d : Fin 2 =>
        if n.val<4 then (0:ℝ) else |gaussianTarget H z (finiteNode n) d|)
        ⟨i.val/2,by omega⟩ ⟨i.val%2,by omega⟩) by
        funext i; by_cases hi : i.val<8 <;> simp [hi,show i.val/2<4 ↔ i.val<8 by omega]]
    rw [sum_fin20_pairs (fun n d => if n.val<4 then (0:ℝ) else |gaussianTarget H z (finiteNode n) d|)]
    apply Finset.sum_congr rfl
    intro n _; by_cases hn : n.val<4 <;> simp [hn]
  rw [he]
  have hb : (∑ n : Fin 10, if n.val<4 then 0 else ∑ d : Fin 2, |gaussianTarget H z (finiteNode n) d|) ≤
      ∑ n : Fin 10, if n.val<4 then 0 else targetEnvelope H (finiteNode n) := by
    apply Finset.sum_le_sum
    intro n _
    split_ifs with hn
    · rfl
    · exact gaussianTarget_pair_bound hz hzB H
        ⟨finiteNode n, by fin_cases n <;> decide +kernel⟩ (by fin_cases n <;> norm_num [finiteNode,residue])
  have he2 : (∑ n : Fin 10, if n.val<4 then 0 else targetEnvelope H (finiteNode n)) = finiteTargetEnvelope := by
    simp [finiteTargetEnvelope,Fin.sum_univ_succ]
  exact hb.trans ((he2 ▸ finiteTargetEnvelope_bound.le).trans (by norm_num [finiteResidualBound]))

def finiteApprox (side : Fin 2) (e : Fin 8 → ℝ) : TrigonometricCoefficients :=
  column (fun i (_ : Unit) => ∑ j : Fin 8, Acoefficient side ⟨i.val,by omega⟩ j*e j)
    (fun _ => (hasSum_fintype _).summable) ()
lemma finiteApprox_norm (side : Fin 2) (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    ‖finiteApprox side e‖ < 3 := by
  rw [l1_norm,tsum_fintype]
  have hb : (∑ i : Fin 22, |∑ j : Fin 8, Acoefficient side i.castSucc j*e j|) ≤
      ∑ i : Fin 23, |∑ j : Fin 8, Acoefficient side i j*e j| := by
    conv_rhs => rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (abs_nonneg _)
  change (∑ i : Fin 22, |∑ j : Fin 8, Acoefficient side i.castSucc j*e j|) < 3
  refine hb.trans_lt ?_
  fin_cases side
  · exact (A1_norm_bound e he).trans (by norm_num)
  · exact (A2_norm_bound e he).trans (by norm_num)

def approximationTailResidual (e : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TailCoefficients :=
  tailTarget z hz hzB +
  (if e.val=0 then CallOperator (finiteApprox 0 (actualParameter z)+finiteApprox 1 (actualParameter z)) -
      AallOperator (finiteApprox 0 (actualParameter z)+finiteApprox 1 (actualParameter z))
    else CallOperator (finiteApprox 1 (actualParameter z)-finiteApprox 0 (actualParameter z)) -
      AallOperator (finiteApprox 0 (actualParameter z)-finiteApprox 1 (actualParameter z)) +
      (12/1000:ℝ) • tailFixedColumn 22)
lemma approximationTailResidual_norm (e : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖approximationTailResidual e z hz hzB‖ ≤ tailResidualBound e := by
  have h1 := (finiteApprox_norm 0 (actualParameter z) (actualParameter_mem hz hzB)).le
  have h2 := (finiteApprox_norm 1 (actualParameter z) (actualParameter_mem hz hzB)).le
  have ht : ‖tailTarget z hz hzB‖ ≤ (1/10^26:ℝ) :=
    (tailTarget_norm hz hzB).trans (tailTargetEnvelope_bound.le.trans (by norm_num))
  have hp : ‖finiteApprox 0 (actualParameter z)+finiteApprox 1 (actualParameter z)‖ ≤ 6 :=
    (norm_add_le _ _).trans (by linarith)
  have hm : ‖finiteApprox 0 (actualParameter z)-finiteApprox 1 (actualParameter z)‖ ≤ 6 :=
    (norm_sub_le _ _).trans (by linarith)
  have hm' : ‖finiteApprox 1 (actualParameter z)-finiteApprox 0 (actualParameter z)‖ ≤ 6 :=
    (norm_sub_le _ _).trans (by linarith)
  have hc (a b : TrigonometricCoefficients) (ha : ‖a‖≤6) (hb : ‖b‖≤6) :
      ‖CallOperator a-AallOperator b‖ ≤ 6*beta := by
    calc
      _ ≤ ‖CallOperator a‖+‖AallOperator b‖ := norm_sub_le _ _
      _ ≤ ‖CallOperator‖*‖a‖+‖AallOperator‖*‖b‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ ‖CallOperator‖*6+‖AallOperator‖*6 := by gcongr
      _ ≤ 6*beta := by nlinarith [AC_all_bound]
  have hv : ‖(12/1000:ℝ) • tailFixedColumn 22‖ ≤ (12/1000:ℝ)*(13/10^8) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<12/1000)]
    exact mul_le_mul_of_nonneg_left (tailFixedColumn_norm_constant.trans (by norm_num)) (by norm_num)
  fin_cases e <;> simp only [approximationTailResidual,tailResidualBound,↓reduceIte,Nat.one_ne_zero]
  · change ‖tailTarget z hz hzB + _‖ ≤ 1/10^26+6*beta+0
    exact (norm_add_le _ _).trans (by linarith [hc _ _ hp hp])
  · change ‖tailTarget z hz hzB + (_+_)‖ ≤ 1/10^26+6*beta+(12/1000)*(13/10^8)
    have hh := (norm_add_le _ _).trans (add_le_add ht
      ((norm_add_le _ _).trans (add_le_add (hc _ _ hm' hm) hv)))
    simpa only [add_assoc] using hh

def actualTailSplit (e : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TailCoefficients :=
  correctionTail e (finiteResidual z) (approximationTailResidual e z hz hzB)
def actualFiniteSplit (e : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : FiniteCoefficients :=
  correctionFinite e (finiteResidual z) (approximationTailResidual e z hz hzB)
lemma actualTailSplit_norm (e : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualTailSplit e z hz hzB‖ ≤ tailErrorBound e :=
  correctionTail_small _ _ _ (finiteResidual_norm hz hzB) (approximationTailResidual_norm e hz hzB)
lemma actualFiniteSplit_norm (e : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualFiniteSplit e z hz hzB‖ ≤ finiteErrorBound e :=
  correctionFinite_small _ _ _ (finiteResidual_norm hz hzB) (approximationTailResidual_norm e hz hzB)

def actualTail (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TailCoefficients :=
  (1/2:ℝ) • (actualTailSplit 0 z hz hzB + (if side.val=0 then actualTailSplit 1 z hz hzB else -actualTailSplit 1 z hz hzB))
def actualFiniteError (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : FiniteCoefficients :=
  (1/2:ℝ) • (actualFiniteSplit 0 z hz hzB + (if side.val=0 then actualFiniteSplit 1 z hz hzB else -actualFiniteSplit 1 z hz hzB))
lemma actualTail_norm (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualTail side z hz hzB‖ < (3/10^9:ℝ) := by
  have hp := actualTailSplit_norm 0 hz hzB
  have hm := actualTailSplit_norm 1 hz hzB
  unfold actualTail
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hh := norm_add_le (actualTailSplit 0 z hz hzB)
    (if side.val=0 then actualTailSplit 1 z hz hzB else -actualTailSplit 1 z hz hzB)
  split_ifs at hh ⊢ <;> (try simp only [norm_neg] at hh) <;> norm_num [tailErrorBound] at hp hm <;> linarith
lemma actualFiniteError_norm (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualFiniteError side z hz hzB‖ < (1/10^5:ℝ) := by
  have hp := actualFiniteSplit_norm 0 hz hzB
  have hm := actualFiniteSplit_norm 1 hz hzB
  unfold actualFiniteError
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hh := norm_add_le (actualFiniteSplit 0 z hz hzB)
    (if side.val=0 then actualFiniteSplit 1 z hz hzB else -actualFiniteSplit 1 z hz hzB)
  split_ifs at hh ⊢ <;> (try simp only [norm_neg] at hh) <;> norm_num [finiteErrorBound] at hp hm <;> linarith
end AtomicTriangular.Construction
end

end OAI
