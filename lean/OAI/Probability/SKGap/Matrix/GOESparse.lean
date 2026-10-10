import Mathlib
import OAI.Probability.SKGap.Matrix.GOESubmatrix
import OAI.Probability.SKGap.Entropy.SparseSubsetEntropy

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def principalOperatorNorm (M : Matrix ι ι ℝ) (S : Finset ι) : ℝ :=
  ‖matrixOperator (M.submatrix (fun i : S=>i.1) (fun i : S=>i.1))‖

omit [Fintype ι] in
lemma principalOperatorNorm_empty (M : Matrix ι ι ℝ) : principalOperatorNorm M ∅=0 := by
  unfold principalOperatorNorm
  have hz : matrixOperator (M.submatrix (fun i : (∅ : Finset ι)=>i.1) (fun i : (∅ : Finset ι)=>i.1))=0 :=
    Subsingleton.elim _ _
  rw [hz,norm_zero]

lemma goe_sparse_one_tail [Nonempty ι] (S : Finset ι) {j α ε : ℝ}
    (hj : 0 < j) (_hα : 0 ≤ α) (hε : 0 < ε) (hS : (S.card:ℝ) ≤ α*(Fintype.card ι:ℝ))
    (hedge : 2*sqrt (j*α) ≤ ε/2) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ε < principalOperatorNorm (goeMatrix (j/(Fintype.card ι:ℝ)) g) S} ≤
      2*exp (-(Fintype.card ι:ℝ)*ε^2/(4*π^2*j)) := by
  by_cases hne : S.Nonempty
  · let : Nonempty S := Finset.Nonempty.to_subtype hne
    have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    let e : S ↪ ι := ⟨Subtype.val,Subtype.val_injective⟩
    have hsqrt : 2*sqrt (j/(Fintype.card ι:ℝ)*(Fintype.card S:ℝ)) ≤ ε/2 := by
      apply le_trans _ hedge
      apply mul_le_mul_of_nonneg_left (sqrt_le_sqrt _) (by norm_num)
      rw [Fintype.card_coe]
      have hm := mul_le_mul_of_nonneg_left hS hj.le
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hn).mpr
      convert hm using 1; ring
    have ht := goe_restricted_norm_tail e (div_pos hj hn) (by positivity : 0 ≤ ε/2)
    apply (measureReal_mono (μ:=gaussianCoordinates (MatrixCoordinates ι)) ?_).trans
      (ht.trans_eq ?_)
    · intro g hg
      change ε < principalOperatorNorm (goeMatrix (j/(Fintype.card ι:ℝ)) g) S at hg
      change 2*sqrt (j/(Fintype.card ι:ℝ)*(Fintype.card S:ℝ))+ε/2 <
        principalOperatorNorm (goeMatrix (j/(Fintype.card ι:ℝ)) g) S
      linarith only [hsqrt,hg]
    · congr 2
      field_simp
      ring
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    simp only [principalOperatorNorm_empty,not_lt_of_ge hε.le,Set.ofPred_false,measureReal_empty]
    positivity

theorem goe_sparse_union_tail [Nonempty ι] {j α ε l : ℝ}
    (hj : 0 < j) (hα : 0 ≤ α) (hε : 0 < ε) (hl : 0 ≤ l)
    (hedge : 2*sqrt (j*α) ≤ ε/2) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ S : Finset ι,(S.card:ℝ) ≤ α*(Fintype.card ι:ℝ) ∧
        ε < principalOperatorNorm (goeMatrix (j/(Fintype.card ι:ℝ)) g) S} ≤
      2*exp (-(Fintype.card ι:ℝ)*(ε^2/(4*π^2*j)-(l*α+log (1+exp (-l))))) := by
  classical
  have he : {g : MatrixCoordinates ι→ℝ | ∃ S : Finset ι,(S.card:ℝ) ≤ α*(Fintype.card ι:ℝ) ∧
        ε < principalOperatorNorm (goeMatrix (j/(Fintype.card ι:ℝ)) g) S} =
      ⋃ S∈smallSupports (ι:=ι) α,{g | ε < principalOperatorNorm (goeMatrix (j/(Fintype.card ι:ℝ)) g) S} := by
    ext g
    simp [smallSupports]
  rw [he]
  apply sparse_union_bound _ _ hl (by norm_num : (0:ℝ) ≤ 2)
  intro S hS
  have hc := (Finset.mem_filter.mp hS).2
  convert goe_sparse_one_tail S hj hα hε hc hedge using 1
  congr 2
  ring
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma supported_quad_eq (M : Matrix ι ι ℝ) (S : Finset ι)
    (w : EuclideanSpace ℝ ι) (hw : ∀ i,i ∉ S → w i=0) :
    matrixQuad M w=matrixQuad (M.submatrix (fun i : S=>i.1) (fun i : S=>i.1))
      (WithLp.toLp 2 (fun i : S=>w i.1)) := by
  change (∑ i,∑ k,w i*M i k*w k)=(∑ i : S,∑ k : S,w i.1*M i.1 k.1*w k.1)
  calc
    _ = ∑ i∈S,∑ k,w i*M i k*w k := (Finset.sum_subset (Finset.subset_univ S) (by
      intro i _ hi
      simp [hw i hi])).symm
    _ = ∑ i : S,∑ k,w i.1*M i.1 k*w k :=
      (Finset.sum_coe_sort S (fun i=>∑ k,w i*M i k*w k)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_coe_sort S (fun k=>w i.1*M i.1 k*w k)]
      exact (Finset.sum_subset (Finset.subset_univ S) (by
        intro k _ hk
        simp [hw k hk])).symm

omit [DecidableEq ι] in
lemma supported_norm_sq_eq (S : Finset ι) (w : EuclideanSpace ℝ ι)
    (hw : ∀ i,i ∉ S → w i=0) :
    ‖WithLp.toLp 2 (fun i : S=>w i.1)‖^2=‖w‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i : S,w i.1^2)=(∑ i,w i^2)
  rw [Finset.sum_coe_sort S (fun i=>w i^2)]
  exact Finset.sum_subset (Finset.subset_univ S) (by intro i _ hi;simp [hw i hi])

lemma supported_quad_le_principal (M : Matrix ι ι ℝ) (S : Finset ι) {ε : ℝ}
    (hM : principalOperatorNorm M S ≤ ε) (w : EuclideanSpace ℝ ι)
    (hw : ∀ i,i ∉ S → w i=0) :
    |⟪w,Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=ι) M w⟫| ≤ ε*‖w‖^2 := by
  rw [← matrixOperator_eq_toEuclideanCLM,← matrixQuad_inner,supported_quad_eq M S w hw,matrixQuad_inner]
  let v := WithLp.toLp 2 (fun i : S=>w i.1)
  calc
    _ ≤ ‖v‖*‖matrixOperator (M.submatrix (fun i : S=>i.1) (fun i : S=>i.1)) v‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖v‖*(principalOperatorNorm M S*‖v‖) :=
      mul_le_mul_of_nonneg_left ((matrixOperator _).le_opNorm v) (norm_nonneg v)
    _ ≤ ‖v‖*(ε*‖v‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hM (norm_nonneg v)) (norm_nonneg v)
    _ = ε*‖w‖^2 := by
      rw [show ‖v‖*(ε*‖v‖)=ε*‖v‖^2 by ring,supported_norm_sq_eq S w hw]
end SKGap

end
end

end OAI
