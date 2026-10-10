import Mathlib
import OAI.Probability.SKGap.Matrix.MatrixQuad
import OAI.Probability.SKGap.Gaussian.GOEGaussian
import OAI.Probability.SKGap.Gaussian.GaussianSquareTail

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators RealInnerProductSpace
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma coordinates_restrict_hasLaw (e : κ ↪ ι) :
    HasLaw (fun g : ι→ℝ=>fun i=>g (e i)) (gaussianCoordinates κ) (gaussianCoordinates ι) := by
  exact iIndepFun.hasLaw_pi (fun i=>coordinate_hasLaw (e i))
    ((iIndepFun_pi (fun _ : ι=>aemeasurable_id)).precomp e.injective)

def matrixCoordinatesEmbedding (e : κ ↪ ι) : MatrixCoordinates κ ↪ MatrixCoordinates ι :=
  (e.prodMap e).sumMap e

omit [Fintype ι] [Fintype κ] in
lemma goeMatrix_submatrix (r : ℝ) (e : κ ↪ ι) (g : MatrixCoordinates ι→ℝ) :
    (goeMatrix r g).submatrix e e=goeMatrix r (fun i=>g (matrixCoordinatesEmbedding e i)) := rfl

lemma continuous_matrixOperator [DecidableEq ι] : Continuous (matrixOperator (ι:=ι)) := by
  let L : Matrix ι ι ℝ →ₗ[ℝ] (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
    { toFun := matrixOperator
      map_add' := by intro A B;ext x i;simp [matrixOperator_apply,Finset.sum_add_distrib,add_mul]
      map_smul' := by intro c A;ext x i;simp [matrixOperator_apply,Finset.mul_sum,mul_assoc] }
  exact L.continuous_of_finiteDimensional

omit [Fintype ι] in
lemma continuous_goeMatrix (r : ℝ) : Continuous (goeMatrix (ι:=ι) r) := by
  unfold goeMatrix
  fun_prop

lemma goe_restricted_norm_tail [DecidableEq κ] [Nonempty κ]
    (e : κ ↪ ι) {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | 2*sqrt (r*(Fintype.card κ:ℝ))+ε < ‖matrixOperator ((goeMatrix r g).submatrix e e)‖} ≤
      2*exp (-ε^2/(π^2*r)) := by
  have hk : (0:ℝ) < Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  have he := coordinates_restrict_hasLaw (matrixCoordinatesEmbedding e)
  have hm : MeasurableSet {g : MatrixCoordinates κ→ℝ |
      2*sqrt (r*(Fintype.card κ:ℝ))+ε < ‖matrixOperator (goeMatrix r g)‖} :=
    measurableSet_lt measurable_const ((continuous_matrixOperator.comp (continuous_goeMatrix r)).norm.measurable)
  simp only [goeMatrix_submatrix]
  rw [he.measureReal_eq hm]
  have ht := goe_norm_tail (ι:=κ) (mul_pos hr hk) hε
  have heq : r*(Fintype.card κ:ℝ)/(Fintype.card κ:ℝ)=r := mul_div_cancel_right₀ _ hk.ne'
  rw [heq] at ht
  convert ht using 1
  congr 2
  field_simp
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma matrix_quad_row_bound (M : Matrix ι ι ℝ) (hM : ∀ i k,M i k=M k i)
    {R : ℝ} (hrow : ∀ i,∑ k,|M i k| ≤ R) (p : EuclideanSpace ℝ ι) :
    |matrixQuad M p| ≤ R*‖p‖^2 := by
  have hsingle (i k : ι) : |p i*M i k*p k| ≤ |M i k| *(p i^2+p k^2)/2 := by
    have hs : 2*|p i| *|p k| ≤ p i^2+p k^2 := by
      nlinarith only [sq_nonneg (|p i|-|p k|),sq_abs (p i),sq_abs (p k)]
    have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg (M i k))
    simp only [abs_mul]
    nlinarith only [hm]
  have hswap : (∑ i,∑ k,|M i k| *p k^2)=(∑ i,∑ k,|M i k| *p i^2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [hM k i]
  calc
    _ ≤ ∑ i,∑ k,|p i*M i k*p k| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _=>Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i,∑ k,|M i k| *(p i^2+p k^2)/2 :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun k _=>hsingle i k))
    _ = ∑ i,(∑ k,|M i k|)*p i^2 := by
      simp only [mul_add,add_div,Finset.sum_add_distrib]
      simp only [← Finset.sum_div]
      rw [hswap]
      simp only [Finset.sum_mul]
      ring
    _ ≤ ∑ i,R*p i^2 := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
    _ = R*‖p‖^2 := by rw [← Finset.mul_sum,EuclideanSpace.norm_sq_eq];simp only [Real.norm_eq_abs,sq_abs]

lemma matrixOperator_norm_le_row (M : Matrix ι ι ℝ) (hM : ∀ i k,M i k=M k i)
    {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ i,∑ k,|M i k| ≤ R) :
    ‖matrixOperator M‖ ≤ R := by
  apply matrixOperator_norm_le_of_quad (by
    ext i k
    simpa only [conjTranspose_apply,star_trivial] using hM k i) hR
  intro p hp
  apply (matrix_quad_row_bound M hM hrow p).trans
  have hs : ‖p‖^2 ≤ 1 := by nlinarith only [hp,norm_nonneg p]
  exact (mul_le_mul_of_nonneg_left hs hR).trans_eq (mul_one R)

lemma matrixOperator_eq_toEuclideanCLM (M : Matrix ι ι ℝ) :
    matrixOperator M=Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=ι) M := by
  ext x i
  rfl
end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_diagonal_hasLaw {r : ℝ} (hr : 0 ≤ r) (i : ι) :
    HasLaw (fun g : MatrixCoordinates ι→ℝ=>goeMatrix r g i i)
      (gaussianReal 0 (Real.toNNReal (2*r))) (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hg := (goe_matrix_gaussian (ι:=ι) r).eval (i,i)
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,goe_mean_zero,← covariance_self hg.aemeasurable,goe_entry_cov hr]
  simp only [ite_true,mul_one]
  congr 2
  ring

lemma goe_diagonal_tail {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | ∃ i : ι,d < |goeMatrix r g i i|} ≤
      2*(Fintype.card ι:ℝ)*exp (-d^2/(8*r)) := by
  have hsingle (i : ι) :
      (gaussianCoordinates (MatrixCoordinates ι)).real {g | d < |goeMatrix r g i i|} ≤
      2*exp (-d^2/(8*r)) := by
    rw [(goe_diagonal_hasLaw hr.le i).measureReal_eq
      (by measurability : MeasurableSet {x : ℝ | d < |x|})]
    convert gaussian_real_abs_tail (r:=2*r) (by positivity) hd using 1
    ring_nf
  have he : {g : MatrixCoordinates ι→ℝ | ∃ i : ι,d < |goeMatrix r g i i|}=
      ⋃ i : ι,{g | d < |goeMatrix r g i i|} := by ext g;simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  apply (Finset.sum_le_sum (fun i _=>hsingle i)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

lemma diagonal_norm_le {d : ℝ} (hd : 0 ≤ d) (v : ι→ℝ) (hv : ∀ i,|v i| ≤ d) :
    ‖Matrix.diagonal v‖ ≤ d := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hd).mpr (fun i=>by simpa only [Real.norm_eq_abs] using hv i)
end SKGap
end
end

end OAI
