import OAI.Analysis.Quantum.DimensionTen.PencilModel

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def pure {n : Type*} (x : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec x (star x)

lemma pure_posSemidef {n : Type*} [Fintype n] (x : n → ℂ) : (pure x).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star x

lemma pure_conjugate {a b : Type*} [Fintype a] (V : Matrix b a ℂ) (x : a → ℂ) :
    V * pure x * Vᴴ = pure (V *ᵥ x) := by
  simp only [pure, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

lemma pure_kronecker {a b : ℕ} (x : Fin a → ℂ) (y : Fin b → ℂ) :
    pure (productVector x y) = pure x ⊗ₖ pure y := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [pure, productVector, Matrix.vecMulVec_apply]
  ring

lemma trace_pure_mul {n : Type*} [Fintype n] (x : n → ℂ) (A : Matrix n n ℂ) :
    Matrix.trace (pure x * A) = star x ⬝ᵥ (A *ᵥ x) := by
  rw [pure, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]

lemma product_dot {a b : ℕ} (x y : Fin a → ℂ) (u v : Fin b → ℂ) :
    star (productVector x u) ⬝ᵥ productVector y v =
      (star x ⬝ᵥ y) * (star u ⬝ᵥ v) := by
  simp only [dotProduct, Fintype.sum_prod_type, productVector, Pi.star_apply,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def omega (a : ℕ) : Fin a × Fin a → ℂ := fun ij => if ij.1 = ij.2 then 1 else 0

lemma choi_eq_amplify {a b : ℕ} (F : Mat a → Mat b) :
    choi F = amplify F a (pure (omega a)) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  change F (Matrix.single i j 1) u v = F (fun p q => pure (omega a) (i,p) (j,q)) u v
  congr 2
  ext p q
  simp [pure, omega, Matrix.single_apply, Matrix.vecMulVec_apply, ite_and]
  split_ifs <;> simp_all

lemma cp_choi_posSemidef {a b : ℕ} (F : Mat a → Mat b) (hF : CompletelyPositive F)
    (ha : 0 < a) : (choi F).PosSemidef := by
  rw [choi_eq_amplify]
  exact hF a ha _ (pure_posSemidef _)

lemma cp_comp {a b c : ℕ} (F : Mat a → Mat b) (G : Mat b → Mat c)
    (hF : CompletelyPositive F) (hG : CompletelyPositive G) :
    CompletelyPositive (G ∘ F) := by
  intro k hk X hX
  exact hG k hk _ (hF k hk X hX)

lemma linear_comp {a b c : ℕ} (F : Mat a → Mat b) (G : Mat b → Mat c)
    (hF : IsComplexLinear F) (hG : IsComplexLinear G) :
    IsComplexLinear (G ∘ F) := by
  constructor
  · intro A B; simp only [Function.comp_apply, hF.1, hG.1]
  · intro c A; simp only [Function.comp_apply, hF.2, hG.2]

lemma eb_choi_separable {a b : ℕ} (F : Mat a → Mat b) (hF : EntanglementBreaking F)
    (ha : 0 < a) : separable (choi F) := by
  rw [choi_eq_amplify]
  exact hF.2 a ha _ (pure_posSemidef _)

end DimensionTen

end
end

end OAI
