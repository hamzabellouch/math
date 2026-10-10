import Mathlib
import OAI.Probability.SKGap.Matrix.GOESubmatrix
import OAI.Probability.SKGap.Localization.TanhCubic

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_l2_norm_le_row (A : Matrix ι ι ℝ) (hA : ∀ i k,A i k=A k i)
    {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ i,∑ k,|A i k| ≤ R) : ‖A‖ ≤ R := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM,← matrixOperator_eq_toEuclideanCLM]
  exact matrixOperator_norm_le_row A hA hR hrow

lemma tanh_matrix_Q_norm (A : Matrix ι ι ℝ) (hA : ∀ i k,A i k=A k i)
    {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ i,∑ k,A i k^2 ≤ R) :
    ‖Matrix.of (fun i k=>tanh (A i k)^2)‖ ≤ R := by
  apply matrix_l2_norm_le_row _ (fun i k=>by simp only [of_apply,hA i k]) hR
  intro i
  apply le_trans _ (hrow i)
  apply Finset.sum_le_sum
  intro k _
  simp only [of_apply,abs_of_nonneg (sq_nonneg (tanh (A i k)))]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (abs_tanh_le_abs (A i k))

lemma tanh_matrix_remainder_norm (A : Matrix ι ι ℝ) (hA : ∀ i k,A i k=A k i)
    {R d : ℝ} (hR : 0 ≤ R) (hd : 0 ≤ d) (hma : ∀ i k,|A i k| ≤ d)
    (hrow : ∀ i,∑ k,A i k^2 ≤ R) :
    ‖Matrix.of (fun i k=>tanh (A i k))-A‖ ≤ d*R/3 := by
  apply matrix_l2_norm_le_row _ (fun i k=>by simp only [Matrix.sub_apply,of_apply,hA i k]) (by positivity)
  intro i
  calc
    _ ≤ ∑ k,d*(A i k)^2/3 := Finset.sum_le_sum (fun k _=>by
      apply (tanh_cubic_error (A i k)).trans
      have h := mul_le_mul_of_nonneg_right (hma i k) (sq_nonneg (A i k))
      have he : |A i k|^3=|A i k| *(A i k)^2 := by rw [pow_succ,sq_abs];ring
      rw [he]
      linarith only [h])
    _ = d*(∑ k,A i k^2)/3 := by rw [Finset.mul_sum,Finset.sum_div]
    _ ≤ d*R/3 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hrow i) hd) (by norm_num)

omit [DecidableEq ι] in
lemma tanh_matrix_fourth_row (A : Matrix ι ι ℝ) {R d : ℝ}
    (hma : ∀ i k,|A i k| ≤ d) (hrow : ∀ i,∑ k,A i k^2 ≤ R) (i : ι) :
    (∑ k,tanh (A i k)^4) ≤ d^2*R := by
  have hentry (k : ι) : tanh (A i k)^4 ≤ d^2*A i k^2 := by
    have habs := abs_tanh_le_abs (A i k)
    have hd : 0 ≤ d := (abs_nonneg _).trans (hma i k)
    have hs : tanh (A i k)^2 ≤ A i k^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr habs
    have hs' : tanh (A i k)^2 ≤ d^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hd).mpr (habs.trans (hma i k))
    have hm := mul_le_mul hs' hs (sq_nonneg _) (sq_nonneg d)
    nlinarith only [hm]
  calc
    _ ≤ ∑ k,d^2*A i k^2 := Finset.sum_le_sum (fun k _=>hentry k)
    _ = d^2*(∑ k,A i k^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg d)
end SKGap

end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators
variable {n : ℕ}

def goeDisorder (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) : Disorder n :=
  fun e=>goeMatrix r g e.1.1 e.1.2

lemma goeDisorder_gaussian (r : ℝ) :
    HasGaussianLaw (goeDisorder (n:=n) r) (gaussianCoordinates (MatrixCoordinates (Fin n))) :=
  (goe_matrix_gaussian (ι:=Fin n) r).map_fun (ContinuousLinearMap.pi (fun e : Edge n=>ContinuousLinearMap.proj e.1))

lemma goeDisorder_mean (r : ℝ) (e : Edge n) :
    (∫ g,goeDisorder r g e ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=0 :=
  goe_mean_zero r e.1.1 e.1.2

lemma goeDisorder_cov {r : ℝ} (hr : 0 ≤ r) (e f : Edge n) :
    cov[fun g=>goeDisorder r g e,fun g=>goeDisorder r g f;
      gaussianCoordinates (MatrixCoordinates (Fin n))]=if e=f then r else 0 := by
  change cov[fun g=>goeMatrix r g e.1.1 e.1.2,fun g=>goeMatrix r g f.1.1 f.1.2;
    gaussianCoordinates (MatrixCoordinates (Fin n))]=_
  rw [goe_entry_cov hr]
  have heq : e=f ↔ e.1.1=f.1.1 ∧ e.1.2=f.1.2 := by simp only [Subtype.ext_iff,Prod.ext_iff]
  have hcross : ¬(e.1.1=f.1.2 ∧ e.1.2=f.1.1) := by
    rintro ⟨h1,h2⟩
    have he := e.2
    rw [h1,h2] at he
    exact (lt_asymm f.2 he)
  split_ifs <;> simp_all

lemma goeDisorder_hasLaw {r : ℝ} (hr : 0 ≤ r) :
    HasLaw (goeDisorder (n:=n) r) (Measure.pi (fun _ : Edge n=>gaussianReal 0 (Real.toNNReal r)))
      (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
  have hg := goeDisorder_gaussian (n:=n) r
  have hl (e : Edge n) : HasLaw (fun g=>goeDisorder r g e)
      (gaussianReal 0 (Real.toNNReal r)) (gaussianCoordinates (MatrixCoordinates (Fin n))) := by
    refine ⟨(hg.eval e).aemeasurable,?_⟩
    rw [(hg.eval e).map_eq_gaussianReal,goeDisorder_mean,
      ← covariance_self (hg.eval e).aemeasurable,goeDisorder_cov hr,ite_eq_left rfl]
  exact iIndepFun.hasLaw_pi hl (hg.iIndepFun_of_covariance_eq_zero
    (fun e f h=>by rw [goeDisorder_cov hr,ite_eq_right h]))

lemma goe_actual_disorder_hasLaw (β : ℝ) (n : ℕ) :
    HasLaw (goeDisorder (n:=n) (β^2/(n:ℝ))) (disorderLaw β n)
      (gaussianCoordinates (MatrixCoordinates (Fin n))) :=
  goeDisorder_hasLaw (by positivity)

lemma coupling_goeDisorder (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) :
    Matrix.of (coupling (goeDisorder r g))=goeMatrix r g-Matrix.diagonal (fun i=>goeMatrix r g i i) := by
  ext i k
  by_cases hik : i=k
  · subst k
    simp [coupling]
  · rcases lt_or_gt_of_ne hik with h | h
    · simp [coupling,h,hik,goeDisorder]
    · simp [coupling,h,not_lt_of_gt h,hik,goeDisorder,goeMatrix,add_comm]
end SKGap

end
end

end OAI
