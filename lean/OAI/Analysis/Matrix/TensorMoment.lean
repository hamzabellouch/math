import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.PositiveTensor

variable {J : Type*} [Fintype J] [DecidableEq J]

/- Finite positive operators are dominated by their trace times identity. -/
theorem trace_domination (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    (Matrix.trace A • (1 : Matrix J J ℂ) - A).PosSemidef := by
  let U := hA.isHermitian.eigenvectorUnitary
  let d : J → ℂ := RCLike.ofReal ∘ hA.isHermitian.eigenvalues
  have ht : Matrix.trace A = ∑ i, d i := hA.isHermitian.trace_eq_sum_eigenvalues
  have hd (i : J) : 0 ≤ Matrix.trace A - d i := by
    rw [ht, sub_nonneg]
    exact Finset.single_le_sum (fun j _ => by
      change (0 : ℂ) ≤ (hA.isHermitian.eigenvalues j : ℂ)
      exact_mod_cast hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hD : (Matrix.diagonal (fun i => Matrix.trace A - d i)).PosSemidef := Matrix.PosSemidef.diagonal hd
  have h := hD.mul_mul_conjTranspose_same (U : Matrix J J ℂ)
  have hU : (U : Matrix J J ℂ) * (U : Matrix J J ℂ).conjTranspose = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hspec : (U : Matrix J J ℂ) * Matrix.diagonal d *
      (U : Matrix J J ℂ).conjTranspose = A := by
    simpa only [U,d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using hA.isHermitian.spectral_theorem.symm
  have he : (Matrix.diagonal (fun i => Matrix.trace A - d i)) =
      Matrix.trace A • (1 : Matrix J J ℂ) - Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [he, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU, hspec] at h
  exact h

/- A positive operator supported on an orthogonal projection is dominated
by the same trace times that projection, with no ambient-dimension loss. -/
theorem projection_trace_domination (A P : Matrix J J ℂ) (hA : A.PosSemidef)
    (hP : P.IsHermitian) (hP2 : P*P=P) (hPA : P*A=A) :
    (Matrix.trace A • P - A).PosSemidef := by
  have h := (trace_domination A hA).mul_mul_conjTranspose_same P
  have hAP : A*P=A := by
    have hh := congrArg Matrix.conjTranspose hPA
    simpa only [Matrix.conjTranspose_mul,hA.isHermitian.eq,hP.eq] using hh
  simpa only [hP.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hP2, hPA, hAP] using h

variable {K : Type*} [Fintype K] [DecidableEq K]

def outer (v : J → ℂ) : Matrix J J ℂ := Matrix.vecMulVec v (star v)

/- Finite Cauchy--Schwarz for a decomposition of the purification vector.
The only loss is the number of actual exception patterns, later polynomial. -/
omit [DecidableEq J] in
theorem outer_sum_domination (v : K → J → ℂ) :
    ((Fintype.card K : ℂ) • (∑ k, outer (v k)) - outer (∑ k, v k)).PosSemidef := by
  let B : Matrix J K ℂ := fun j k => v k j
  let e : K → ℂ := fun _ => 1
  have h := trace_domination (outer e) (Matrix.posSemidef_vecMulVec_self_star e)
  have ht : Matrix.trace (outer e) = (Fintype.card K : ℂ) := by simp [Matrix.trace, outer, e, Matrix.vecMulVec]
  rw [ht] at h
  have hc := h.mul_mul_conjTranspose_same B
  have hBB : B*B.conjTranspose = ∑ k, outer (v k) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.sum_apply]
    rfl
  have hBe : B*outer e*B.conjTranspose = outer (∑ k, v k) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, outer, Matrix.vecMulVec_apply,
      Pi.star_apply]
    simp only [B, e, star_one, mul_one, Finset.sum_apply, star_sum]
    rw [← Finset.mul_sum]
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hBB, hBe] using hc

/- The literal finite partial trace; it is a sum of positive submatrices. -/
def partialTrace (A : Matrix (J × K) (J × K) ℂ) : Matrix J J ℂ := fun i j => ∑ k, A (i,k) (j,k)

omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_posSemidef (A : Matrix (J × K) (J × K) ℂ) (hA : A.PosSemidef) :
    (partialTrace A).PosSemidef := by
  have he : partialTrace A = ∑ k, A.submatrix (fun i => (i,k)) (fun i => (i,k)) := by
    ext i j
    simp [partialTrace, Matrix.sum_apply]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun k _ => hA.submatrix _)

omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_outer_matrix (A : Matrix J K ℂ) :
    partialTrace (outer (fun x : J × K => A x.1 x.2)) = A*A.conjTranspose := by
  ext i j
  simp [partialTrace, outer, Matrix.vecMulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
end CoordinateSweeps.PositiveTensor
namespace CoordinateSweeps.PositiveTensor
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

def productMatrix (r : I → Matrix A A ℂ) : Matrix (I → A) (I → A) ℂ :=
  fun u w => ∏ i, r i (u i) (w i)

omit [DecidableEq A] in
lemma productMatrix_mul (r t : I → Matrix A A ℂ) :
    productMatrix (fun i => r i * t i) = productMatrix r * productMatrix t := by
  ext u w
  simp only [productMatrix,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact Finset.prod_mul_distrib

omit [DecidableEq I] [Fintype A] [DecidableEq A] in
lemma productMatrix_star (r : I → Matrix A A ℂ) :
    productMatrix (fun i => (r i).conjTranspose) = (productMatrix r).conjTranspose := by
  ext u w
  simp [productMatrix,Matrix.conjTranspose_apply]

omit [DecidableEq I] [Fintype A] [DecidableEq A] in
lemma productMatrix_smul (c : I → ℂ) (r : I → Matrix A A ℂ) :
    productMatrix (fun i => c i • r i) = (∏ i, c i) • productMatrix r := by
  ext u w
  simp only [productMatrix,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

lemma productMatrix_posSemidef (r : I → Matrix A A ℂ) (hr : ∀ i, (r i).PosSemidef) :
    (productMatrix r).PosSemidef := by
  have h (i : I) : ∃ b : Matrix A A ℂ, r i = b.conjTranspose*b := by
    simpa only [Matrix.star_eq_conjTranspose] using
      CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hr i).nonneg
  choose b hb using h
  rw [show r = (fun i => (b i).conjTranspose*b i) from funext hb]
  rw [productMatrix_mul,productMatrix_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype A] [DecidableEq A] in
lemma productMatrix_sum {K : Type*} [Fintype K] (r : I → K → Matrix A A ℂ) :
    productMatrix (fun i => ∑ k, r i k) = ∑ w : I → K, productMatrix (fun i => r i (w i)) := by
  ext u v
  simp only [productMatrix,Matrix.sum_apply]
  exact Fintype.prod_sum (fun i k => r i k (u i) (v i))

lemma productMatrix_mono (r t : I → Matrix A A ℂ) (hr : ∀ i, (r i).PosSemidef)
    (ht : ∀ i, (t i - r i).PosSemidef) :
    (productMatrix t - productMatrix r).PosSemidef := by
  let f : I → Bool → Matrix A A ℂ := fun i b => if b then t i-r i else r i
  have hsum (i : I) : ∑ b : Bool, f i b = t i := by
    simp [f]
  have he : productMatrix r = productMatrix (fun i => f i (false)) := by simp [f]
  rw [he,show t = (fun i => ∑ b : Bool, f i b) from (funext hsum).symm,productMatrix_sum]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (fun _ : I => false)),add_sub_cancel_right]
  apply Matrix.posSemidef_sum
  intro w _
  apply productMatrix_posSemidef
  intro i
  cases w i <;> simp only [f,Bool.false_eq_true,↓reduceIte]
  · exact hr i
  · exact ht i

omit [DecidableEq A] in
lemma productMatrix_trace (r : I → Matrix A A ℂ) :
    Matrix.trace (productMatrix r) = ∏ i, Matrix.trace (r i) := by
  change (∑ w : I → A, ∏ i, r i (w i) (w i)) = ∏ i, ∑ a, r i a a
  exact (Fintype.prod_sum (fun i a => r i a a)).symm

/- The pure product of possibly different pair amplitudes has the expected
literal partial trace. No graded tensor convention is used in this identity. -/
omit [DecidableEq A] in
lemma pair_product_partialTrace (z : I → Matrix A A ℂ) (u v : I → A) :
    (∑ w : I → A, (∏ i, z i (u i) (w i)) * star (∏ i, z i (v i) (w i))) =
      productMatrix (fun i => z i*(z i).conjTranspose) u v := by
  simp only [productMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,star_prod]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => z i (u i) a * star (z i (v i) a))).symm
end CoordinateSweeps.PositiveTensor

namespace CoordinateSweeps.PositiveTensor
variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

def inclusion (e : K ↪ J) : Matrix J K ℂ := fun j k => if j=e k then 1 else 0

omit [Fintype J] in
lemma inclusion_mulVec_image (e : K ↪ J) (v : K → ℂ) (k : K) :
    (inclusion e).mulVec v (e k) = v k := by
  simp [Matrix.mulVec,dotProduct,inclusion,e.injective.eq_iff]

omit [Fintype J] [DecidableEq K] in
lemma inclusion_mulVec_notin (e : K ↪ J) (v : K → ℂ) (j : J)
    (hj : j ∉ Set.range e) : (inclusion e).mulVec v j = 0 := by
  have hne (k : K) : j ≠ e k := fun he => hj ⟨k,he.symm⟩
  simp [Matrix.mulVec,dotProduct,inclusion,hne]

omit [Fintype K] in
lemma inclusion_isometry (e : K ↪ J) : (inclusion e).conjTranspose * inclusion e = 1 := by
  ext k k'
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,inclusion]
  rw [Finset.sum_eq_single (e k)]
  · by_cases h : k=k' <;> simp [h,e.injective.eq_iff,Matrix.one_apply]
  · intro j _ hj
    simp [hj]
  · simp

omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma mul_outer_mul_star (B : Matrix J K ℂ) (v : K → ℂ) :
    B * Matrix.vecMulVec v (star v) * B.conjTranspose =
      Matrix.vecMulVec (B.mulVec v) (star (B.mulVec v)) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.vecMulVec_apply,Matrix.conjTranspose_apply,
    Pi.star_apply,Matrix.mulVec,dotProduct,star_sum,star_mul]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma inclusion_trace_outer (e : K ↪ J) (v : K → ℂ) :
    Matrix.trace (Matrix.vecMulVec ((inclusion e).mulVec v) (star ((inclusion e).mulVec v))) =
      Matrix.trace (Matrix.vecMulVec v (star v)) := by
  rw [← mul_outer_mul_star,Matrix.trace_mul_cycle,inclusion_isometry,Matrix.one_mul]
end CoordinateSweeps.PositiveTensor
namespace CoordinateSweeps.PositiveTensor
variable {J K L : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype L]
omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_sub (A B : Matrix (J × K) (J × K) ℂ) :
    partialTrace (A-B) = partialTrace A-partialTrace B := by
  ext i j
  simp [partialTrace,Finset.sum_sub_distrib]
omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_smul (c : ℂ) (A : Matrix (J × K) (J × K) ℂ) :
    partialTrace (c • A) = c • partialTrace A := by
  ext i j
  simp [partialTrace,Matrix.smul_apply,Finset.mul_sum]
omit [Fintype J] [DecidableEq J] [DecidableEq K] in
lemma partialTrace_sum (A : L → Matrix (J × K) (J × K) ℂ) :
    partialTrace (∑ k, A k) = ∑ k, partialTrace (A k) := by
  ext i j
  simp only [partialTrace,Matrix.sum_apply]
  exact Finset.sum_comm
end CoordinateSweeps.PositiveTensor
namespace CoordinateSweeps.PositiveTensor
variable {J : Type*} [Fintype J] [DecidableEq J]
omit [Fintype J] [DecidableEq J] in
lemma domination_pad (A B : Matrix J J ℂ) (a b : ℂ) (hB : B.PosSemidef) (hab : a ≤ b)
    (h : (a • B-A).PosSemidef) : (b • B-A).PosSemidef := by
  have hh := (hB.smul (sub_nonneg.mpr hab)).add h
  convert hh using 1
  module
omit [Fintype J] [DecidableEq J] in
lemma domination_trans (A B C : Matrix J J ℂ) (a b : ℂ) (ha : 0 ≤ a)
    (hAB : (a • B-A).PosSemidef) (hBC : (b • C-B).PosSemidef) :
    ((a*b) • C-A).PosSemidef := by
  have h := (hBC.smul ha).add hAB
  convert h using 1
  module
end CoordinateSweeps.PositiveTensor
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CoordinateSweeps.DependentTensor
variable {I : Type*} [Fintype I] [DecidableEq I] {J : I → Type*}
  [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

def tensor (A : ∀ i, Matrix (J i) (J i) ℂ) : Matrix (∀ i, J i) (∀ i, J i) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

omit [∀ index, DecidableEq (J index)] in
lemma tensor_mul (A B : ∀ i, Matrix (J i) (J i) ℂ) :
    tensor (fun i => A i*B i)=tensor A*tensor B := by
  ext x y
  simp only [tensor,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.prod_mul_distrib

omit [DecidableEq I] [∀ index, Fintype (J index)] [∀ index, DecidableEq (J index)] in
lemma tensor_star (A : ∀ i, Matrix (J i) (J i) ℂ) :
    tensor (fun i => (A i).conjTranspose)=(tensor A).conjTranspose := by
  ext x y
  simp [tensor,Matrix.conjTranspose_apply]

omit [∀ index, DecidableEq (J index)] in
lemma tensor_trace (A : ∀ i, Matrix (J i) (J i) ℂ) :
    Matrix.trace (tensor A)=∏ i, Matrix.trace (A i) := by
  simp only [Matrix.trace,Matrix.diag,tensor]
  exact (Fintype.prod_sum (fun i => fun j : J i => A i j j)).symm

omit [DecidableEq I] [∀ index, Fintype (J index)] in
lemma tensor_one : tensor (fun i => (1 : Matrix (J i) (J i) ℂ))=1 := by
  classical
  ext x y
  by_cases h : x=y
  · subst y; simp [tensor]
  · obtain ⟨i,hi⟩:=Function.ne_iff.mp h
    simp only [tensor,Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hi

lemma tensor_pow (A : ∀ i, Matrix (J i) (J i) ℂ) (q : ℕ) :
    tensor (fun i => A i^q)=(tensor A)^q := by
  induction q with
  | zero => simpa using tensor_one
  | succ q ih => simp only [pow_succ,tensor_mul,ih]

lemma tensor_moment (A : ∀ i, Matrix (J i) (J i) ℂ) (q : ℕ) :
    Matrix.trace (((tensor A).conjTranspose*tensor A)^q)=
      ∏ i, Matrix.trace (((A i).conjTranspose*A i)^q) := by
  rw [← tensor_star,← tensor_mul,← tensor_pow,tensor_trace]

open scoped MatrixOrder in
lemma tensor_posSemidef (A : ∀ i, Matrix (J i) (J i) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (tensor A).PosSemidef := by
  choose B hB using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hA i).nonneg
  have he : A=fun i => (B i).conjTranspose*B i := by funext i; exact hB i
  rw [he,tensor_mul,tensor_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq I] [∀ index, Fintype (J index)] [∀ index, DecidableEq (J index)] in
lemma tensor_smul (c : I → ℂ) (A : ∀ i, Matrix (J i) (J i) ℂ) :
    tensor (fun i => c i • A i)=(∏ i, c i) • tensor A := by
  ext x y
  simp only [tensor,Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]

omit [∀ index, Fintype (J index)] [∀ index, DecidableEq (J index)] in
lemma tensor_sum {K : I → Type*} [∀ i, Fintype (K i)]
    (A : ∀ i, K i → Matrix (J i) (J i) ℂ) :
    tensor (fun i => ∑ k, A i k)=∑ x : ∀ i, K i, tensor (fun i => A i (x i)) := by
  ext a b
  simp only [tensor,Matrix.sum_apply]
  exact Fintype.prod_sum _

/- Tensor positivity is monotone in every factor simultaneously. -/
lemma tensor_mono (A B : ∀ i, Matrix (J i) (J i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hAB : ∀ i, (B i-A i).PosSemidef) :
    (tensor B-tensor A).PosSemidef := by
  classical
  let F (i : I) (b : Bool) := if b then B i-A i else A i
  have he : B=(fun i => ∑ b : Bool, F i b) := by
    funext i
    simp [F]
  have ht : tensor B=∑ x : I → Bool, tensor (fun i => F i (x i)) := by
    rw [he,tensor_sum]
  have hzero : tensor (fun i => F i ((fun _ => false) i))=tensor A := by simp [F]
  have hs := Finset.sum_erase_add (Finset.univ : Finset (I → Bool))
    (fun x => tensor (fun i => F i (x i))) (Finset.mem_univ (fun _ => false))
  rw [hzero,← ht] at hs
  have hdiff : tensor B-tensor A =
      ∑ x ∈ Finset.univ.erase (fun _ : I => false), tensor (fun i => F i (x i)) := by
    exact (eq_sub_of_add_eq hs).symm
  rw [hdiff]
  apply Matrix.posSemidef_sum
  intro x hx
  apply tensor_posSemidef
  intro i
  dsimp [F]
  split_ifs
  · exact hAB i
  · exact hA i

/- Exact finite mixtures can be tensored without losing normalization. -/
omit [∀ index, Fintype (J index)] [∀ index, DecidableEq (J index)] in
lemma tensor_mixture {K : I → Type*} [∀ i, Fintype (K i)]
    (w : ∀ i, K i → ℂ) (A : ∀ i, K i → Matrix (J i) (J i) ℂ) :
    tensor (fun i => ∑ k, w i k • A i k)=
      ∑ x : ∀ i, K i, (∏ i, w i (x i)) • tensor (fun i => A i (x i)) := by
  rw [tensor_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact tensor_smul _ _

end CoordinateSweeps.DependentTensor
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.TensorBoard
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def tensor (A : I → Matrix J J ℂ) : Matrix (I → J) (I → J) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

omit [DecidableEq J] in
lemma tensor_mul (A B : I → Matrix J J ℂ) :
    tensor (fun i => A i*B i)=tensor A*tensor B := by
  ext x y
  simp only [tensor,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.prod_mul_distrib

omit [DecidableEq I] [Fintype J] [DecidableEq J] in
lemma tensor_star (A : I → Matrix J J ℂ) :
    tensor (fun i => (A i).conjTranspose)=(tensor A).conjTranspose := by
  ext x y
  simp [tensor,Matrix.conjTranspose_apply]

omit [DecidableEq J] in
lemma tensor_trace (A : I → Matrix J J ℂ) :
    Matrix.trace (tensor A)=∏ i, Matrix.trace (A i) := by
  simp only [Matrix.trace,Matrix.diag,tensor]
  exact (Fintype.prod_sum (fun i : I => fun j : J => A i j j)).symm

omit [DecidableEq I] [Fintype J] in
lemma tensor_one : tensor (fun _ : I => (1 : Matrix J J ℂ))=1 := by
  classical
  ext x y
  by_cases h : x=y
  · subst y; simp [tensor]
  · have hn : ∃ i, x i ≠ y i := Function.ne_iff.mp h
    obtain ⟨i,hi⟩:=hn
    simp only [tensor,Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hi

open scoped MatrixOrder in
lemma tensor_posSemidef (A : I → Matrix J J ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (tensor A).PosSemidef := by
  choose B hB using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hA i).nonneg
  have he : A=fun i => (B i).conjTranspose*B i := by
    funext i
    exact hB i
  rw [he,tensor_mul,tensor_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

open scoped MatrixOrder in
lemma trace_mul_nonneg {A B : Matrix J J ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A*B) := by
  obtain ⟨C,rfl⟩:=CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [Matrix.star_eq_conjTranspose,Matrix.trace_mul_cycle,Matrix.trace_mul_cycle]
  exact (hB.mul_mul_conjTranspose_same C).trace_nonneg

lemma trace_mono_right {A B C : Matrix J J ℂ} (h : (B-A).PosSemidef)
    (hC : C.PosSemidef) : Matrix.trace (A*C) ≤ Matrix.trace (B*C) := by
  have hh:=trace_mul_nonneg h hC
  rw [sub_mul,Matrix.trace_sub] at hh
  exact sub_nonneg.mp hh

/- The source's deleted-site AMGM loss exp(h), using x≤exp(x−1).
This avoids unnecessary equal-size/nonempty column cases. -/
lemma free_product_le_exp {T : Type*} [Fintype T] (F : Finset T) (x : T → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i ≤ Fintype.card T) :
    ∏ i ∈ F, x i ≤ Real.exp (Fintype.card T-F.card) := by
  calc
    _ ≤ ∏ i ∈ F, Real.exp (x i-1) := by
      apply Finset.prod_le_prod₀ (fun index _ => hx index)
      intro i hi
      linarith [Real.add_one_le_exp (x i-1)]
    _ = Real.exp (∑ i ∈ F, (x i-1)) := by rw [Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      rw [Finset.sum_sub_distrib,Finset.sum_const, nsmul_eq_mul,mul_one]
      have hh : ∑ i ∈ F, x i ≤ ∑ i, x i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hx i)
      linarith)

omit [Fintype I] [DecidableEq J] in
lemma free_tensor_trace (F : Finset I) (A B C : I → Matrix J J ℂ) :
    Matrix.trace (tensor (fun i : F => A i.val) * tensor (fun i : F => B i.val) *
      tensor (fun i : F => C i.val)) = ∏ i : F, Matrix.trace (A i.val*B i.val*C i.val) := by
  rw [← tensor_mul,← tensor_mul,tensor_trace]

end CoordinateSweeps.TensorBoard

namespace CoordinateSweeps.TensorBoard
variable {R C J : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] [DecidableEq C] [Fintype J] [DecidableEq J]

/- Regularization is genuine positive definite, not an inverse assumption. -/
omit [DecidableEq R] [Fintype J] in
lemma average_regularization_posDef (r : R → Matrix J J ℂ)
    (hr : ∀ i, (r i).PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (((Fintype.card R : ℂ)⁻¹) • ∑ i, r i) + (ε : ℂ) • (1 : Matrix J J ℂ) |>.PosDef := by
  apply Matrix.PosDef.posSemidef_add
  · exact (Matrix.posSemidef_sum _ (fun i _ => hr i)).smul (by positivity)
  · exact Matrix.PosDef.one.smul (by exact_mod_cast hε : (0 : ℂ) < ε)

open scoped MatrixOrder CFC in
lemma exists_whitening (B : Matrix J J ℂ) (hB : B.PosDef) :
    ∃ A : Matrix J J ℂ, A.PosSemidef ∧ A*B*A=1 ∧
      ∀ D : Matrix J J ℂ, Commute B D → Commute A D := by
  refine ⟨B ^ (-(1/2) : ℝ), Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg,
    CFC.conjugate_rpow_neg_one_half B hB.isStrictlyPositive, ?_⟩
  intro D hD
  exact hD.cfc_nnreal _

omit [DecidableEq R] in
lemma whitening_sum_bound (r : R → Matrix J J ℂ)
    (B A : Matrix J J ℂ) (hA : A.IsHermitian) (hABA : A*B*A=1)
    (hB : (B-((Fintype.card R : ℂ)⁻¹) • ∑ i, r i).PosSemidef) :
    ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef := by
  have h := hB.mul_mul_conjTranspose_same A
  rw [hA.eq,Matrix.mul_sub,Matrix.sub_mul,hABA,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_sum,Matrix.sum_mul] at h
  have hh := h.smul (show (0 : ℂ) ≤ Fintype.card R by positivity)
  have hc : (Fintype.card R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa only [smul_sub,smul_smul,mul_inv_cancel₀ hc,one_smul] using hh

omit [DecidableEq R] [Nonempty R] in
lemma trace_whitened_sum_le (r : R → Matrix J J ℂ)
    (v A : Matrix J J ℂ) (hv : v.PosSemidef) (ht : Matrix.trace v=1)
    (hw : ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef) :
    ∑ i, (Matrix.trace (A*r i*A*v)).re ≤ Fintype.card R := by
  have hh:=trace_mono_right hw hv
  simp only [Matrix.sum_mul,Matrix.trace_sum,Matrix.smul_mul,one_mul,Matrix.trace_smul,ht] at hh
  simpa only [Complex.re_sum,smul_eq_mul,mul_one,Complex.natCast_re] using (Complex.le_def.mp hh).1

/- Exact exp(h) loss from deleted sites, with the whitening condition that
will be supplied by the constructed regularized average. -/
omit [Nonempty R] in
theorem board_trace_le (F : Finset (R × C)) (r : R → Matrix J J ℂ)
    (v : C → Matrix J J ℂ) (hr : ∀ i, (r i).PosSemidef)
    (hv : ∀ j, (v j).PosSemidef) (ht : ∀ j, Matrix.trace (v j)=1)
    (A : Matrix J J ℂ) (hA : A.IsHermitian)
    (hw : ((Fintype.card R : ℂ) • (1 : Matrix J J ℂ)-∑ i, A*r i*A).PosSemidef) :
    (Matrix.trace (tensor (fun x : F => A*r x.val.1*A) *
      tensor (fun x : F => v x.val.2))).re ≤
        Real.exp (Fintype.card R*Fintype.card C-F.card) := by
  let t (x : R × C) : ℂ := Matrix.trace (A*r x.1*A*v x.2)
  have hn (x : R × C) : 0 ≤ t x := by
    apply trace_mul_nonneg _ (hv x.2)
    simpa only [hA.eq] using (hr x.1).mul_mul_conjTranspose_same A
  have he (x : R × C) : ((t x).re : ℂ)=t x := by
    apply Complex.ext
    · rfl
    · simpa using (Complex.nonneg_iff.mp (hn x)).2
  have hs : ∑ x : R × C, (t x).re ≤ Fintype.card (R × C) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    calc
      _ ≤ ∑ _ : C, (Fintype.card R : ℝ) := Finset.sum_le_sum (fun j _ => trace_whitened_sum_le r (v j) A (hv j) (ht j) hw)
      _ = _ := by simp [Fintype.card_prod]; ring
  have hh := free_product_le_exp F (fun x => (t x).re)
    (fun x => (Complex.nonneg_iff.mp (hn x)).1) hs
  rw [← tensor_mul,tensor_trace]
  have hp : (∏ x : F, t x.val).re=∏ x ∈ F, (t x).re := by
    have he' : ∏ x : F, t x.val= (∏ x : F, (t x.val).re : ℝ) := by
      push_cast
      exact Finset.prod_congr rfl (fun x _ => (he x.val).symm)
    calc
      _ = ∏ x : F, (t x.val).re := by simpa only [Complex.ofReal_re] using congrArg Complex.re he'
      _ = _ := Finset.prod_coe_sort F (fun x => (t x).re)
  change (∏ x : F, t x.val).re ≤ _
  rw [hp]
  simpa only [Fintype.card_prod,Nat.cast_mul] using hh

end CoordinateSweeps.TensorBoard
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps
theorem norm_entry_le_matrix_norm {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin D) : ‖A i j‖ ≤ ‖A‖ := by
  let v : EuclideanSpace ℂ (Fin D) := EuclideanSpace.single j 1
  have hv : ‖v‖ = 1 := by simp [v]
  have h := A.l2_opNorm_mulVec v
  have hi := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin D) ℂ).symm (A.mulVec v)) i
  have he : ((EuclideanSpace.equiv (Fin D) ℂ).symm (A.mulVec v)) i = A i j := by
    simp [v]
  rw [he] at hi
  rw [hv, mul_one] at h
  exact hi.trans h

theorem norm_trace_le {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) :
    ‖Matrix.trace A‖ ≤ D * ‖A‖ := by
  calc
    ‖Matrix.trace A‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin D, ‖A‖ := Finset.sum_le_sum (fun i _ => norm_entry_le_matrix_norm A i i)
    _ = D * ‖A‖ := by simp

theorem trace_moment_nonneg {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (q : ℕ) :
    0 ≤ (Matrix.trace ((A.conjTranspose * A)^q)).re :=
  ((Matrix.posSemidef_conjTranspose_mul_self A).pow q).trace_nonneg.1

theorem trace_moment_le {D : ℕ} [NeZero D] (A : Matrix (Fin D) (Fin D) ℂ) (q : ℕ) :
    (Matrix.trace ((A.conjTranspose * A)^q)).re ≤ D * ‖A‖^(2*q) := by
  calc
    _ ≤ ‖Matrix.trace ((A.conjTranspose * A)^q)‖ := Complex.re_le_norm _
    _ ≤ D * ‖(A.conjTranspose * A)^q‖ := norm_trace_le _
    _ ≤ D * ‖A.conjTranspose * A‖^q :=
      mul_le_mul_of_nonneg_left (norm_pow_le _ _) (Nat.cast_nonneg _)
    _ = D * ‖A‖^(2*q) := by rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two, ← pow_mul]

theorem matrix_unitary_norm_le {D : ℕ} [NeZero D] (A : Matrix (Fin D) (Fin D) ℂ)
    (hA : A.conjTranspose * A = 1) : ‖A‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self A
  rw [hA] at h
  have h1 : ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤ 1 := le_of_eq (norm_one)
  nlinarith [norm_nonneg A]

theorem unitary_average_norm_le {D : ℕ} [NeZero D] {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (A : Ω → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ x, (A x).conjTranspose * A x = 1) :
    ‖∑ x, (w x : ℂ) • A x‖ ≤ 1 := by
  calc
    _ ≤ ∑ x, ‖(w x : ℂ) • A x‖ := norm_sum_le _ _
    _ = ∑ x, w x * ‖A x‖ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw x)]
    _ ≤ ∑ x, w x := Finset.sum_le_sum (fun x _ =>
      mul_le_of_le_one_right (hw x) (matrix_unitary_norm_le (A x) (hA x)))
    _ = 1 := hs

/- Ordinary, unnormalized even Schatten moment. For a matrix K this is
Tr((K* K)^q), NOT divided by its dimension. -/
def schattenMoment {D : ℕ} (q : ℕ) (K : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (Matrix.trace ((K.conjTranspose * K) ^ q)).re
end CoordinateSweeps
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
