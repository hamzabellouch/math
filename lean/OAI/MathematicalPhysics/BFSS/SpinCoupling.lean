import Mathlib

namespace OAI

/-! Spin-one-half Casimir algebra and invertible shifted tensor couplings. -/

namespace BFSSSpinHalf
noncomputable section
section Algebra
variable {R : Type*} [Ring R] [Algebra ℝ R]

omit [Algebra ℝ R] in
lemma tensor_mul (A B C D : R) (h : Commute B C) :
    (A*B)*(C*D) = (A*C)*(B*D) := by
  calc
    _ = A*(B*C)*D := by noncomm_ring
    _ = A*(C*B)*D := by rw [h.eq]
    _ = _ := by noncomm_ring

lemma coupled_diagonal (J L : R) (hc : Commute L J)
    (hL : L*L = (-1/4 : ℝ) • (1 : R)) :
    (J*L)*(J*L) = (-1/4 : ℝ) • (J*J) := by
  rw [tensor_mul J L J L hc,hL,mul_smul_comm,mul_one]

lemma coupled_pair (J K U L P Q : R) (hLK : Commute L K) (hPJ : Commute P J)
    (hJK : J*K-K*J = U)
    (hLP : L*P = (1/2 : ℝ) • Q) (hPL : P*L = (-1/2 : ℝ) • Q) :
    (J*L)*(K*P)+(K*P)*(J*L) = (1/2 : ℝ) • (U*Q) := by
  rw [tensor_mul J L K P hLK,tensor_mul K P J L hPJ,hLP,hPL]
  calc
    _ = (1/2 : ℝ) • ((J*K-K*J)*Q) := by
      simp only [mul_smul_comm,sub_mul,smul_sub]
      module
    _ = _ := by rw [hJK]

theorem casimir_identity (J L : Fin 3 → R) (hc : ∀ i j, Commute (L i) (J j))
    (hJ01 : J 0*J 1-J 1*J 0 = J 2)
    (hJ12 : J 1*J 2-J 2*J 1 = J 0)
    (hJ20 : J 2*J 0-J 0*J 2 = J 1)
    (hL : ∀ i, L i*L i = (-1/4 : ℝ) • (1 : R))
    (hL01 : L 0*L 1 = (1/2 : ℝ) • L 2)
    (hL10 : L 1*L 0 = (-1/2 : ℝ) • L 2)
    (hL12 : L 1*L 2 = (1/2 : ℝ) • L 0)
    (hL21 : L 2*L 1 = (-1/2 : ℝ) • L 0)
    (hL20 : L 2*L 0 = (1/2 : ℝ) • L 1)
    (hL02 : L 0*L 2 = (-1/2 : ℝ) • L 1) :
    let S := J 0*L 0+J 1*L 1+J 2*L 2
    S*S = (-1/4 : ℝ) • (J 0*J 0+J 1*J 1+J 2*J 2)+(1/2 : ℝ) • S := by
  dsimp only
  calc
    _ = (J 0*L 0)*(J 0*L 0)+(J 1*L 1)*(J 1*L 1)+(J 2*L 2)*(J 2*L 2)+
      ((J 0*L 0)*(J 1*L 1)+(J 1*L 1)*(J 0*L 0))+
      ((J 1*L 1)*(J 2*L 2)+(J 2*L 2)*(J 1*L 1))+
      ((J 2*L 2)*(J 0*L 0)+(J 0*L 0)*(J 2*L 2)) := by noncomm_ring
    _ = _ := by
      rw [coupled_diagonal _ _ (hc 0 0) (hL 0),coupled_diagonal _ _ (hc 1 1) (hL 1),
        coupled_diagonal _ _ (hc 2 2) (hL 2),
        coupled_pair _ _ _ _ _ _ (hc 0 1) (hc 1 0) hJ01 hL01 hL10,
        coupled_pair _ _ _ _ _ _ (hc 1 2) (hc 2 1) hJ12 hL12 hL21,
        coupled_pair _ _ _ _ _ _ (hc 2 0) (hc 0 2) hJ20 hL20 hL02]
      module
end Algebra

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem shift_norm_lower (J : Fin 3 → E →ₗ[ℝ] E) (S : E →ₗ[ℝ] E)
    (hJ : ∀ i x y, inner ℝ (J i x) y = -inner ℝ x (J i y))
    (hS : ∀ x y, inner ℝ (S x) y = inner ℝ x (S y))
    (hpoly : S*S = (-1/4 : ℝ) • (J 0*J 0+J 1*J 1+J 2*J 2)+(1/2 : ℝ) • S)
    (x : E) : (1/2 : ℝ)*‖x‖ ≤ ‖(3/2 : ℝ) • x-(4 : ℝ) • S x‖ := by
  let A : E →ₗ[ℝ] E := (3/2 : ℝ) • (1 : Module.End ℝ E)-(4 : ℝ) • S
  have hA (u v : E) : inner ℝ (A u) v = inner ℝ u (A v) := by
    change inner ℝ ((3/2 : ℝ) • u-(4 : ℝ) • S u) v =
      inner ℝ u ((3/2 : ℝ) • v-(4 : ℝ) • S v)
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hS]
  have hp : A*A-A-(3/4 : ℝ) • (1 : Module.End ℝ E) =
      (-4 : ℝ) • (J 0*J 0+J 1*J 1+J 2*J 2) := by
    dsimp only [A]
    simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_smul,
      one_mul,mul_one,hpoly,smul_add]
    module
  have h := congrArg (fun T : E →ₗ[ℝ] E => inner ℝ x (T x)) hp
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.add_apply,
    Module.End.mul_apply,Module.End.one_apply,inner_sub_right,inner_add_right,
    real_inner_smul_right,←hA x (A x)] at h
  simp only [real_inner_self_eq_norm_sq] at h
  have hjj (i : Fin 3) : inner ℝ x (J i (J i x)) = -‖J i x‖^2 := by
    have hi := hJ i x (J i x)
    rw [real_inner_self_eq_norm_sq] at hi
    linarith
  rw [hjj 0,hjj 1,hjj 2] at h
  have habs := neg_le_abs (inner ℝ x (A x))
  have hinner := abs_real_inner_le_norm x (A x)
  have hb : (3/4 : ℝ)*‖x‖^2 ≤ ‖A x‖^2+‖x‖*‖A x‖ := by
    nlinarith [sq_nonneg ‖J 0 x‖,sq_nonneg ‖J 1 x‖,sq_nonneg ‖J 2 x‖]
  change (1/2 : ℝ)*‖x‖ ≤ ‖A x‖
  nlinarith [norm_nonneg x,norm_nonneg (A x)]
end Hilbert
end
end BFSSSpinHalf

namespace BFSSSpinHalf
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def eucAlg : Matrix ι ι ℝ ≃ₐ[ℝ] Module.End ℝ (EuclideanSpace ℝ ι) :=
  Matrix.toLinAlgEquiv (EuclideanSpace.basisFun ι ℝ).toBasis

lemma eucAlg_eq (A : Matrix ι ι ℝ) : eucAlg A = Matrix.toEuclideanLin A := rfl

lemma transpose_inner (A : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    inner ℝ (eucAlg A x) y = inner ℝ x (eucAlg A.transpose y) := by
  have hh := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A) x y
  rw [←Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hh
  exact hh.symm

lemma skew_inner (A : Matrix ι ι ℝ) (hA : A.transpose = -A)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (eucAlg A x) y = -inner ℝ x (eucAlg A y) := by
  rw [transpose_inner,hA,map_neg,LinearMap.neg_apply,inner_neg_right]

lemma symmetric_inner (A : Matrix ι ι ℝ) (hA : A.transpose = A)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (eucAlg A x) y = inner ℝ x (eucAlg A y) := by
  rw [transpose_inner,hA]

theorem matrix_shift_trivial_kernel (J : Fin 3 → Matrix ι ι ℝ) (S : Matrix ι ι ℝ)
    (hJ : ∀ i, (J i).transpose = -J i) (hS : S.transpose = S)
    (hpoly : S*S = (-1/4 : ℝ) • (J 0*J 0+J 1*J 1+J 2*J 2)+(1/2 : ℝ) • S)
    (x : EuclideanSpace ℝ ι)
    (hx : eucAlg ((3/2 : ℝ) • (1 : Matrix ι ι ℝ)-(4 : ℝ) • S) x = 0) : x = 0 := by
  have hp := congrArg (eucAlg (ι := ι)) hpoly
  simp only [map_mul,map_add,map_smul] at hp
  have hb := shift_norm_lower (fun i => eucAlg (J i)) (eucAlg S)
    (fun i => skew_inner _ (hJ i)) (symmetric_inner _ hS) hp x
  simp only [map_sub,map_smul,map_one,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply] at hx
  rw [hx,norm_zero] at hb
  exact norm_eq_zero.mp (by linarith [norm_nonneg x])
end
end BFSSSpinHalf

namespace BFSSSpinHalf
noncomputable section
open scoped Kronecker
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma skew_matrix_of_inner (A : Matrix ι ι ℝ)
    (hA : ∀ x y, inner ℝ (eucAlg A x) y = -inner ℝ x (eucAlg A y)) :
    A.transpose = -A := by
  apply eucAlg.injective
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [transpose_inner,Matrix.transpose_transpose,map_neg,LinearMap.neg_apply,inner_neg_left]
  linarith [hA x y]

def leftLift : Matrix ι ι ℝ →ₐ[ℝ] Matrix (ι × κ) (ι × κ) ℝ where
  toFun A := A ⊗ₖ (1 : Matrix κ κ ℝ)
  map_one' := Matrix.one_kronecker_one
  map_zero' := Matrix.zero_kronecker _
  map_add' := fun A B => Matrix.add_kronecker A B _
  map_mul' := fun A B => by rw [←Matrix.mul_kronecker_mul,mul_one]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one,Matrix.smul_kronecker,Matrix.one_kronecker_one]

def rightLift : Matrix κ κ ℝ →ₐ[ℝ] Matrix (ι × κ) (ι × κ) ℝ where
  toFun A := (1 : Matrix ι ι ℝ) ⊗ₖ A
  map_one' := Matrix.one_kronecker_one
  map_zero' := Matrix.kronecker_zero _
  map_add' := fun A B => Matrix.kronecker_add _ A B
  map_mul' := fun A B => by rw [←Matrix.mul_kronecker_mul,mul_one]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one,Matrix.kronecker_smul,Matrix.one_kronecker_one]

lemma lifts_commute (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    Commute (leftLift A) (rightLift B) := by
  change A ⊗ₖ (1 : Matrix κ κ ℝ) * (1 : Matrix ι ι ℝ) ⊗ₖ B =
    (1 : Matrix ι ι ℝ) ⊗ₖ B * A ⊗ₖ (1 : Matrix κ κ ℝ)
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,mul_one,one_mul,one_mul,mul_one]

lemma leftLift_transpose (A : Matrix ι ι ℝ) :
    (leftLift (κ := κ) A).transpose = leftLift A.transpose := by
  change (A ⊗ₖ (1 : Matrix κ κ ℝ)).transpose = A.transpose ⊗ₖ (1 : Matrix κ κ ℝ)
  rw [←Matrix.kroneckerMap_transpose,Matrix.transpose_one]

lemma rightLift_transpose (B : Matrix κ κ ℝ) :
    (rightLift (ι := ι) B).transpose = rightLift B.transpose := by
  change ((1 : Matrix ι ι ℝ) ⊗ₖ B).transpose = (1 : Matrix ι ι ℝ) ⊗ₖ B.transpose
  rw [←Matrix.kroneckerMap_transpose,Matrix.transpose_one]
end
end BFSSSpinHalf

end OAI
