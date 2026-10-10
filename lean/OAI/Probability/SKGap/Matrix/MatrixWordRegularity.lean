import Mathlib
import OAI.Probability.SKGap.Matrix.MatrixEntryCLM
import OAI.Probability.SKGap.Matrix.OpNormDiagonal

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

def matrixFactorProduct (F : List (X→Matrix ι ι ℝ)) (x : X) : Matrix ι ι ℝ :=
  (F.map (fun f=>f x)).prod

omit [PseudoMetricSpace X] in
@[simp] lemma matrixFactorProduct_nil (x : X) : matrixFactorProduct ([] : List (X→Matrix ι ι ℝ)) x=1 := rfl
omit [PseudoMetricSpace X] in
@[simp] lemma matrixFactorProduct_cons (f : X→Matrix ι ι ℝ) (F : List (X→Matrix ι ι ℝ)) (x : X) :
    matrixFactorProduct (f::F) x=f x*matrixFactorProduct F x := rfl

omit [PseudoMetricSpace X] in
lemma matrixFactorProduct_opNorm (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R) (x : X) :
    opNorm (matrixFactorProduct F x) ≤ (R:ℝ)^F.length := by
  induction F with
  | nil => simpa using opNorm_one_le (ι:=ι)
  | cons f F ih =>
    rw [matrixFactorProduct_cons,List.length_cons,pow_succ']
    exact (opNorm_mul _ _).trans (mul_le_mul (hF f (List.mem_cons_self) x)
      (ih (fun p hp=>hF p (List.mem_cons_of_mem f hp))) (show 0 ≤ opNorm (matrixFactorProduct F x) from norm_nonneg _) R.coe_nonneg)

theorem matrixFactorProduct_lipschitz (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R)
    (hL : ∀ f∈F,LipschitzWith R f) :
    LipschitzWith ((F.length:NNReal)*R^F.length) (matrixFactorProduct F) := by
  induction F with
  | nil => simp [matrixFactorProduct]
  | cons f F ih =>
    have hFt : ∀ p∈F,∀ x,opNorm (p x) ≤ R := fun p hp=>hF p (List.mem_cons_of_mem f hp)
    have hLt : ∀ p∈F,LipschitzWith R p := fun p hp=>hL p (List.mem_cons_of_mem f hp)
    have ht := ih hFt hLt
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,matrixFactorProduct_cons,matrixFactorProduct_cons]
    have he : f x*matrixFactorProduct F x-f y*matrixFactorProduct F y=
        f x*(matrixFactorProduct F x-matrixFactorProduct F y)+(f x-f y)*matrixFactorProduct F y := by noncomm_ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply (add_le_add (frobenius_mul_le_opNorm _ _) (frobenius_mul_le_opNorm_right _ _)).trans
    have hd : ‖matrixFactorProduct F x-matrixFactorProduct F y‖ ≤ ((F.length:ℝ)*(R:ℝ)^F.length)*dist x y := by
      simpa only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow] using ht.dist_le_mul x y
    have hf : ‖f x-f y‖ ≤ (R:ℝ)*dist x y := by
      simpa only [dist_eq_norm] using (hL f List.mem_cons_self).dist_le_mul x y
    have hb := matrixFactorProduct_opNorm F hFt y
    have hp := hF f List.mem_cons_self x
    have h1 := mul_le_mul hp hd (norm_nonneg _) R.coe_nonneg
    have h2 := mul_le_mul hf hb (show 0 ≤ opNorm (matrixFactorProduct F y) from norm_nonneg _) (mul_nonneg R.coe_nonneg dist_nonneg)
    apply (add_le_add h1 h2).trans_eq
    norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow,List.length_cons,Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one,pow_succ]
    ring

lemma matrixFactorProduct_entry_lipschitz (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) (i k : ι) :
    LipschitzWith ((F.length:NNReal)*R^F.length) (fun x=>matrixFactorProduct F x i k) := by
  simpa only [one_mul,Function.comp_def] using (matrixEntry_lipschitz i k).comp (matrixFactorProduct_lipschitz F hF hL)

lemma matrixFactorProduct_trace_lipschitz (F : List (X→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ x,opNorm (f x) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) :
    LipschitzWith (⟨sqrt (Fintype.card ι),sqrt_nonneg _⟩*((F.length:NNReal)*R^F.length))
      (fun x=>trace (matrixFactorProduct F x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (matrixFactorProduct_lipschitz F hF hL).dist_le_mul x y
  have ht := abs_trace_le_frobenius (matrixFactorProduct F x-matrixFactorProduct F y)
  rw [trace_sub] at ht
  have hm := mul_le_mul_of_nonneg_left hh (sqrt_nonneg (Fintype.card ι:ℝ))
  change |trace (matrixFactorProduct F x)-trace (matrixFactorProduct F y)| ≤
    (sqrt (Fintype.card ι)*((F.length:ℝ)*(R:ℝ)^F.length))*dist x y
  simpa only [dist_eq_norm,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow,mul_assoc] using ht.trans hm

lemma goe_word_entry_lipschitz (F : List (Matrix ι ι ℝ→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f)
    (r : ℝ) (i k : ι) :
    LipschitzWith (((F.length:NNReal)*R^F.length)*⟨sqrt (2*r),sqrt_nonneg _⟩)
      (fun z : EuclideanSpace ℝ (MatrixCoordinates ι)=>matrixFactorProduct F (goeMatrix r z) i k) :=
  (matrixFactorProduct_entry_lipschitz F hF hL i k).comp (goeMatrix_L2_lipschitz r)

lemma goe_word_normalized_trace_lipschitz (F : List (Matrix ι ι ℝ→Matrix ι ι ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) (r : ℝ) :
    LipschitzWith (⟨(Fintype.card ι:ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg _)⟩*
      (⟨sqrt (Fintype.card ι),sqrt_nonneg _⟩*((F.length:NNReal)*R^F.length))*⟨sqrt (2*r),sqrt_nonneg _⟩)
      (fun z : EuclideanSpace ℝ (MatrixCoordinates ι)=>trace (matrixFactorProduct F (goeMatrix r z))/(Fintype.card ι:ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hg := (goeMatrix_L2_lipschitz (ι:=ι) r).dist_le_mul z w
  have ht := (matrixFactorProduct_trace_lipschitz F hF hL).dist_le_mul (goeMatrix r z) (goeMatrix r w)
  change dist (goeMatrix r z) (goeMatrix r w) ≤ sqrt (2*r)*dist z w at hg
  change dist (trace (matrixFactorProduct F (goeMatrix r z))) (trace (matrixFactorProduct F (goeMatrix r w))) ≤
    (sqrt (Fintype.card ι)*((F.length:ℝ)*(R:ℝ)^F.length))*dist (goeMatrix r z) (goeMatrix r w) at ht
  have hc : 0 ≤ sqrt (Fintype.card ι)*((F.length:ℝ)*(R:ℝ)^F.length) := by positivity
  have hi : 0 ≤ (Fintype.card ι:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hb := mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_left hg hc)) hi
  change dist (trace (matrixFactorProduct F (goeMatrix r z))/(Fintype.card ι:ℝ))
    (trace (matrixFactorProduct F (goeMatrix r w))/(Fintype.card ι:ℝ)) ≤
    ((Fintype.card ι:ℝ)⁻¹*(sqrt (Fintype.card ι)*((F.length:ℝ)*(R:ℝ)^F.length))*sqrt (2*r))*dist z w
  rw [Real.dist_eq,← sub_div,abs_div]
  simp only [abs_of_nonneg (show (0:ℝ) ≤ (Fintype.card ι:ℝ) by positivity)]
  simpa only [Real.dist_eq,div_eq_mul_inv,mul_assoc,mul_comm (Fintype.card ι:ℝ)⁻¹] using hb
end SKGap
end
end

end OAI
