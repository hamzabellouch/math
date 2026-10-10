import Mathlib
import OAI.Probability.SKRatio.Quantization.BinGeometry

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

def matrixInner (A B : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j*B i j

lemma matrixInner_symm (A B : Matrix ι ι ℝ) : matrixInner A B=matrixInner B A := by
  simp only [matrixInner,mul_comm]

lemma matrixInner_add_left (A B C : Matrix ι ι ℝ) :
    matrixInner (A+B) C=matrixInner A C+matrixInner B C := by
  simp [matrixInner,add_mul,Finset.sum_add_distrib]

lemma matrixInner_add_right (A B C : Matrix ι ι ℝ) :
    matrixInner A (B+C)=matrixInner A B+matrixInner A C := by
  simp [matrixInner,mul_add,Finset.sum_add_distrib]

lemma matrixInner_transpose (A B : Matrix ι ι ℝ) :
    matrixInner Aᵀ Bᵀ=matrixInner A B := by
  unfold matrixInner
  exact Finset.sum_comm

lemma matrixInner_transpose_left (A B : Matrix ι ι ℝ) :
    matrixInner Aᵀ B=matrixInner A Bᵀ := by
  simpa only [Matrix.transpose_transpose] using matrixInner_transpose A Bᵀ

lemma matrixInner_sq_sub (A B : Matrix ι ι ℝ) :
    (∑ i, ∑ j, (A i j-B i j)^2)=matrixInner A A+matrixInner B B-2*matrixInner A B := by
  simp only [matrixInner,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def linearMatrix (σ : ι → α) (C : α → α → ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => u i*C (σ i) (σ j)

def quadraticMatrix (σ : ι → α) (K : α → α → ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => K (σ i) (σ j)*u i*u j

def binVariance (σ : ι → α) (C : α → α → ℝ) (a : α) : ℝ :=
  ∑ j, C a (σ j)^2

omit [Fintype α] [DecidableEq α] in
lemma binVariance_nonneg (σ : ι → α) (C : α → α → ℝ) (a : α) :
    0 ≤ binVariance σ C a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma linearMatrix_inner (σ : ι → α) (C : α → α → ℝ) (u z : ι → ℝ) :
    matrixInner (linearMatrix σ C u) (linearMatrix σ C z) =
      ∑ a, overlap σ u z a*binVariance σ C a := by
  unfold matrixInner linearMatrix
  have he (i j : ι) : u i*C (σ i) (σ j)*(z i*C (σ i) (σ j)) =
      (u i*z i)*C (σ i) (σ j)^2 := by ring
  simp_rw [he,←Finset.mul_sum]
  exact sum_weighted σ (fun i => u i*z i) (binVariance σ C)

lemma linearMatrix_cross_zero {σ : ι → α} (C : α → α → ℝ) {u : ι → ℝ}
    (hu : ZeroSum σ u) (z : ι → ℝ) :
    matrixInner (linearMatrix σ C u) (linearMatrix σ C z)ᵀ=0 := by
  unfold matrixInner linearMatrix
  change (∑ i, ∑ j, u i*C (σ i) (σ j)*(z j*C (σ j) (σ i)))=0
  convert zero_sum_bilinear hu z (fun a d => C a d*C d a) using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma quadraticMatrix_transpose (σ : ι → α) (K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) (u : ι → ℝ) : (quadraticMatrix σ K u)ᵀ=quadraticMatrix σ K u := by
  ext i j
  simp only [quadraticMatrix,Matrix.transpose_apply,hK (σ j) (σ i)]
  ring

lemma linear_quadratic_inner_zero {σ : ι → α} (C K : α → α → ℝ) (u : ι → ℝ)
    {z : ι → ℝ} (hz : ZeroSum σ z) :
    matrixInner (linearMatrix σ C u) (quadraticMatrix σ K z)=0 := by
  unfold matrixInner linearMatrix quadraticMatrix
  apply Finset.sum_eq_zero
  intro i _
  convert zero_sum_weighted hz (fun d => u i*z i*C (σ i) d*K (σ i) d) using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadraticMatrix_inner (σ : ι → α) (K : α → α → ℝ) (u z : ι → ℝ) :
    matrixInner (quadraticMatrix σ K u) (quadraticMatrix σ K z)=
      ∑ a, ∑ d, K a d^2*overlap σ u z a*overlap σ u z d := by
  have he (i j : ι) : (K (σ i) (σ j)*u i*u j)*(K (σ i) (σ j)*z i*z j)=
      (u i*z i)*(u j*z j)*K (σ i) (σ j)^2 := by ring
  unfold matrixInner quadraticMatrix
  simp_rw [he]
  rw [double_weighted σ (fun i => u i*z i) (fun i => u i*z i) (fun a d => K a d^2)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  change overlap σ u z a*overlap σ u z d*K a d^2= _
  ring

def residualMatrix (σ : ι → α) (C K : α → α → ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  linearMatrix σ C u+(linearMatrix σ C u)ᵀ+quadraticMatrix σ K u

lemma residualMatrix_inner {σ : ι → α} (C K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) {u z : ι → ℝ}
    (hu : ZeroSum σ u) (hz : ZeroSum σ z) :
    matrixInner (residualMatrix σ C K u) (residualMatrix σ C K z)=
      2*(∑ a, overlap σ u z a*binVariance σ C a)+
        ∑ a, ∑ d, K a d^2*overlap σ u z a*overlap σ u z d := by
  unfold residualMatrix
  simp only [matrixInner_add_left,matrixInner_add_right]
  rw [matrixInner_transpose_left _ (quadraticMatrix σ K z),quadraticMatrix_transpose σ K hK z]
  rw [matrixInner_symm (quadraticMatrix σ K u) _,matrixInner_symm (quadraticMatrix σ K u) _]
  rw [matrixInner_transpose_left _ (quadraticMatrix σ K u),quadraticMatrix_transpose σ K hK u]
  simp only [linearMatrix_cross_zero C hu,linear_quadratic_inner_zero C K u hz,
    linear_quadratic_inner_zero C K z hu,matrixInner_transpose_left,Matrix.transpose_transpose,
    linearMatrix_inner,quadraticMatrix_inner,add_zero,zero_add]
  ring

lemma residualMatrix_increment {σ : ι → α} (C K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) {u z : ι → ℝ} {s : α → ℝ}
    (hu : ZeroSum σ u) (hz : ZeroSum σ z)
    (hus : overlap σ u u=s) (hzs : overlap σ z z=s) :
    (∑ i, ∑ j, (residualMatrix σ C K u i j-residualMatrix σ C K z i j)^2) ≤
      4*∑ a, (s a-overlap σ u z a)*(binVariance σ C a+∑ d, K a d^2*s d) := by
  rw [matrixInner_sq_sub,residualMatrix_inner C K hK hu hu,
    residualMatrix_inner C K hK hz hz,residualMatrix_inner C K hK hu hz,hus,hzs]
  let q := overlap σ u z
  have hq : ∀ a, q a ≤ s a := overlap_le hus hzs
  have hineq : (∑ a, ∑ d, K a d^2*(s a*s d-q a*q d)) ≤
      ∑ a, ∑ d, K a d^2*(s a*(s d-q d)+s d*(s a-q a)) := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro d _
    exact mul_le_mul_of_nonneg_left (overlap_product_bound hq a d) (sq_nonneg _)
  have he : (∑ a, ∑ d, K a d^2*(s a*(s d-q d)+s d*(s a-q a))) =
      2*∑ a, (s a-q a)*(∑ d, K a d^2*s d) := by
    simp only [mul_add,Finset.sum_add_distrib]
    have hs : (∑ a, ∑ d, K a d^2*(s a*(s d-q d))) =
        ∑ a, ∑ d, K a d^2*(s d*(s a-q a)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro d _
      rw [hK d a]
    rw [hs]
    rw [two_mul]
    congr 1 <;> apply Finset.sum_congr rfl
    all_goals
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
  rw [he] at hineq
  have he1 : (∑ a, ∑ d, K a d^2*(s a*s d-q a*q d)) =
      (∑ a, ∑ d, K a d^2*s a*s d)-(∑ a, ∑ d, K a d^2*q a*q d) := by
    simp only [mul_sub,Finset.sum_sub_distrib,mul_assoc]
  have he2 : (∑ a, (s a-q a)*(binVariance σ C a+∑ d, K a d^2*s d)) =
      (∑ a, s a*binVariance σ C a)-(∑ a, q a*binVariance σ C a)+
        ∑ a, (s a-q a)*(∑ d, K a d^2*s d) := by
    simp only [mul_add,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [he1] at hineq
  change _ ≤ 4*∑ a, (s a-q a)*(binVariance σ C a+∑ d, K a d^2*s d)
  rw [he2]
  dsimp only [q] at hineq
  dsimp only [q]
  linarith only [hineq]

end SKRatio.Bins

end

end OAI
