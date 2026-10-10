import OAI.Analysis.Quantum.DimensionTen.PureMatrices
import OAI.Analysis.Quantum.DimensionTen.TensorKraus

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def asLinearMap {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F) :
    Mat a →ₗ[ℂ] Mat b where
  toFun := F
  map_add' := hF.1
  map_smul' := hF.2

lemma matrix_expansion {a : ℕ} (A : Mat a) :
    A = ∑ i : Fin a, ∑ j : Fin a, A i j • Matrix.single i j 1 := by
  ext i j
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

lemma linear_expansion {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F) (A : Mat a) :
    F A = ∑ i : Fin a, ∑ j : Fin a, A i j • F (Matrix.single i j 1) := by
  calc
    F A = F (∑ i, ∑ j, A i j • Matrix.single i j 1) := congrArg F (matrix_expansion A)
    _ = _ := by
      change asLinearMap F hF _ = _
      simp only [map_sum, map_smul, asLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

lemma choi_trace_pairing {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F)
    (A : Mat a) (B : Mat b) :
    Matrix.trace ((A ⊗ₖ B) * choi F) = Matrix.trace (B * F Aᵀ) := by
  rw [linear_expansion F hF Aᵀ]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, choi, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.transpose_apply, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma choi_product_dot {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    star (productVector u v) ⬝ᵥ (choi F *ᵥ productVector u v) =
      Matrix.trace (pure v * F (pure u)ᵀ) := by
  rw [← trace_pure_mul, pure_kronecker, choi_trace_pairing F hF]

lemma kraus_trace_adjoint {r a b : Type*} [Fintype r] [Fintype a] [Fintype b]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    Matrix.trace (A * krausMap (fun k => (Q k)ᴴ) B) =
      Matrix.trace (krausMap Q A * B) := by
  simp only [krausMap, Matrix.conjTranspose_conjTranspose, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    Matrix.trace (A * ((Q k)ᴴ * B * Q k)) =
      Matrix.trace ((A * (Q k)ᴴ * B) * Q k) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Q k * (A * (Q k)ᴴ * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
