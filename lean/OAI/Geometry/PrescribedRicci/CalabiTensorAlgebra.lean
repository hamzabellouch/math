import Mathlib

namespace OAI

/-! Calabi Tensor Algebra. -/

noncomputable section
open Matrix
open scoped Kronecker ComplexOrder MatrixOrder
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev TensorIndex (n : Type*) := n × (n × n)

def tensor3 (L U V : Matrix n n ℂ) : Matrix (TensorIndex n) (TensorIndex n) ℂ :=
  L ⊗ₖ (U ⊗ₖ V)

omit [Fintype n] [DecidableEq n] in
lemma tensor3_apply (L U V : Matrix n n ℂ) (i j : TensorIndex n) :
    tensor3 L U V i j = L i.1 j.1*(U i.2.1 j.2.1*V i.2.2 j.2.2) := rfl

omit [DecidableEq n] in
lemma tensor3_mul (L U V L' U' V' : Matrix n n ℂ) :
    tensor3 L U V*tensor3 L' U' V' = tensor3 (L*L') (U*U') (V*V') := by
  simp only [tensor3,← Matrix.mul_kronecker_mul]

omit [Fintype n] in
lemma tensor3_one : tensor3 (1 : Matrix n n ℂ) 1 1 = 1 := by
  simp only [tensor3,Matrix.one_kronecker_one]

lemma tensor3_mulVec_left (L : Matrix n n ℂ) (T : TensorIndex n → ℂ) (a k j : n) :
    (tensor3 L 1 1*ᵥ T) (a,k,j) = ∑ v, L a v*T (v,k,j) := by
  classical
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tensor3_apply,
    Matrix.one_apply,mul_ite,ite_mul]

lemma tensor3_mulVec_middle (U : Matrix n n ℂ) (T : TensorIndex n → ℂ) (a k j : n) :
    (tensor3 1 U 1*ᵥ T) (a,k,j) = ∑ v, U k v*T (a,v,j) := by
  classical
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tensor3_apply,
    Matrix.one_apply,mul_ite,ite_mul]

lemma tensor3_mulVec_right (V : Matrix n n ℂ) (T : TensorIndex n → ℂ) (a k j : n) :
    (tensor3 1 1 V*ᵥ T) (a,k,j) = ∑ v, V j v*T (a,k,v) := by
  classical
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tensor3_apply,
    Matrix.one_apply,mul_ite,ite_mul]

def tensorMetric (H : Matrix n n ℂ) : Matrix (TensorIndex n) (TensorIndex n) ℂ :=
  tensor3 H⁻¹.transpose H H⁻¹.transpose

def tensorConnection (G : Matrix n n ℂ) : Matrix (TensorIndex n) (TensorIndex n) ℂ :=
  tensor3 (-G.transpose) 1 1+tensor3 1 G 1+tensor3 1 1 (-G.transpose)

lemma tensorMetric_posDef {H : Matrix n n ℂ} (hH : H.PosDef) : (tensorMetric H).PosDef :=
  hH.inv.transpose.kronecker (hH.kronecker hH.inv.transpose)

lemma tensorConnection_mulVec (G : Matrix n n ℂ) (T : TensorIndex n → ℂ) (a k j : n) :
    (tensorConnection G*ᵥ T) (a,k,j) = ∑ v, G k v*T (a,v,j)-
      (∑ v, G v a*T (v,k,j))-(∑ v, G v j*T (a,k,v)) := by
  simp only [tensorConnection,Matrix.add_mulVec,Pi.add_apply,tensor3_mulVec_left,
    tensor3_mulVec_middle,tensor3_mulVec_right,Matrix.neg_apply,Matrix.transpose_apply,
    neg_mul,Finset.sum_neg_distrib]
  ring

lemma tensorMetric_mul_connection (H G : Matrix n n ℂ) :
    tensorMetric H*tensorConnection G =
      tensor3 (H⁻¹.transpose*(-G.transpose)) H H⁻¹.transpose+
      tensor3 H⁻¹.transpose (H*G) H⁻¹.transpose+
      tensor3 H⁻¹.transpose H (H⁻¹.transpose*(-G.transpose)) := by
  simp only [tensorMetric,tensorConnection,Matrix.mul_add,tensor3_mul,mul_one]

end MongeAmpere

end

end OAI
