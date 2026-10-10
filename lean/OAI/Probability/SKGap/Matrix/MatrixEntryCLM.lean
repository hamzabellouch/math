import Mathlib
import OAI.Probability.SKGap.Localization.FrobeniusSq

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_entry_le_frobenius (M : Matrix ι ι ℝ) (i k : ι) : |M i k| ≤ ‖M‖ := by
  have h₁ : (M i k)^2 ≤ ∑ j, (M i j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have h₂ : (∑ j, (M i j)^2) ≤ ∑ a,∑ j, (M a j)^2 :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ i)
  have hh : (M i k)^2 ≤ ‖M‖^2 := by rw [frobenius_sq]; exact h₁.trans h₂
  nlinarith only [hh,sq_abs (M i k),abs_nonneg (M i k),norm_nonneg M]

noncomputable def matrixEntryCLM (i k : ι) : Matrix ι ι ℝ →L[ℝ] ℝ :=
  ({ toFun := fun M => M i k
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Matrix ι ι ℝ →ₗ[ℝ] ℝ).mkContinuous 1
      (fun M => by simpa [Real.norm_eq_abs] using! matrix_entry_le_frobenius M i k)

lemma matrixEntry_lipschitz (i k : ι) : LipschitzWith 1 (fun M : Matrix ι ι ℝ => M i k) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simpa only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul,Matrix.sub_apply] using!
    matrix_entry_le_frobenius (M-N) i k

omit [DecidableEq ι] in
lemma matrixEntry_derivative {f : ℝ → Matrix ι ι ℝ} {v : Matrix ι ι ℝ} {t : ℝ}
    (hf : HasDerivAt f v t) (i k : ι) : HasDerivAt (fun s => f s i k) (v i k) t := by
  classical
  exact (matrixEntryCLM i k).hasFDerivAt.comp_hasDerivAt t hf

lemma matrix_inverse_diff_bound (K B E : Matrix ι ι ℝ) :
    ‖K*B*E*K‖ ≤ opNorm K*(opNorm B*‖E‖)*opNorm K := by
  calc
    _ ≤ ‖K*B*E‖*opNorm K := frobenius_mul_le_opNorm_right _ _
    _ = ‖K*(B*E)‖*opNorm K := by rw [mul_assoc K B E]
    _ ≤ (opNorm K*‖B*E‖)*opNorm K :=
      mul_le_mul_of_nonneg_right (frobenius_mul_le_opNorm _ _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (frobenius_mul_le_opNorm _ _) (norm_nonneg _)) (norm_nonneg _)

noncomputable def diagonalVector (M : Matrix ι ι ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => M i i)

lemma diagonalVector_norm_le (M : Matrix ι ι ℝ) : ‖diagonalVector M‖ ≤ ‖M‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg M)
  simp only [← sq]
  rw [EuclideanSpace.norm_sq_eq,frobenius_sq]
  apply Finset.sum_le_sum
  intro i _
  simpa only [diagonalVector,Real.norm_eq_abs,sq_abs] using
    (Finset.single_le_sum (fun j _ => sq_nonneg (M i j)) (Finset.mem_univ i))

lemma abs_trace_le_frobenius (M : Matrix ι ι ℝ) :
    |Matrix.trace M| ≤ sqrt (Fintype.card ι)*‖M‖ := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)
  have hv : ‖v‖ = sqrt (Fintype.card ι) := by
    rw [EuclideanSpace.norm_eq]; simp [v]
  have hi := abs_real_inner_le_norm (diagonalVector M) v
  change |∑ i, 1*M i i| ≤ ‖diagonalVector M‖*‖v‖ at hi
  simp only [one_mul,hv] at hi
  change |Matrix.trace M| ≤ ‖diagonalVector M‖*sqrt (Fintype.card ι) at hi
  exact hi.trans ((mul_le_mul_of_nonneg_right (diagonalVector_norm_le M) (sqrt_nonneg _)).trans_eq (mul_comm _ _))

lemma matrixTrace_mul_lipschitz {Ω : Type*} [PseudoMetricSpace Ω]
    {K : Ω → Matrix ι ι ℝ} {L : ℝ≥0} (hK : LipschitzWith L K)
    (B : Matrix ι ι ℝ) :
    LipschitzWith (⟨sqrt (Fintype.card ι)*opNorm B,by exact mul_nonneg (sqrt_nonneg _) (norm_nonneg _)⟩*L)
      (fun x => Matrix.trace (K x*B)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |Matrix.trace (K x*B)-Matrix.trace (K y*B)| ≤
    (sqrt (Fintype.card ι)*opNorm B*(L:ℝ))*dist x y
  rw [← Matrix.trace_sub,← sub_mul]
  calc
    _ ≤ sqrt (Fintype.card ι)*‖(K x-K y)*B‖ := abs_trace_le_frobenius _
    _ ≤ sqrt (Fintype.card ι)*(‖K x-K y‖*opNorm B) :=
      mul_le_mul_of_nonneg_left (frobenius_mul_le_opNorm_right _ _) (sqrt_nonneg _)
    _ ≤ sqrt (Fintype.card ι)*(((L:ℝ)*dist x y)*opNorm B) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using hK.dist_le_mul x y)
          (norm_nonneg _)) (sqrt_nonneg _)
    _ = _ := by ring

end SKGap

noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology

end
end
end
end
end

end OAI
