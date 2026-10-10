import OAI.Analysis.Quantum.DimensionTen.Kraus

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma sum_kronecker {r a b c d : Type*} [Fintype r]
    (A : r → Matrix a b ℂ) (B : Matrix c d ℂ) :
    (∑ r, A r) ⊗ₖ B = ∑ r, A r ⊗ₖ B := by
  ext i j
  simp [Matrix.sum_apply, Finset.sum_mul]

lemma kronecker_sum {r a b c d : Type*} [Fintype r]
    (A : Matrix a b ℂ) (B : r → Matrix c d ℂ) :
    A ⊗ₖ (∑ r, B r) = ∑ r, A ⊗ₖ B r := by
  ext i j
  simp [Matrix.sum_apply, Finset.mul_sum]

lemma block_expansion {a c : ℕ} (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    X = ∑ i : Fin c, ∑ j : Fin c,
      (Matrix.of (fun a b => X (a, i) (b, j))) ⊗ₖ (Matrix.single i j 1) := by
  ext ⟨u, i⟩ ⟨v, j⟩
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

lemma sum_four_comm {a b c d M : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [AddCommMonoid M] (f : a → b → c → d → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]

lemma tensorMap_kraus {r s : Type*} [Fintype r] [Fintype s] {a b c d : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (R : s → Matrix (Fin d) (Fin c) ℂ)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap (krausMap Q) (krausMap R) X =
      krausMap (fun p : r × s => Q p.1 ⊗ₖ R p.2) X := by
  conv_rhs => arg 2; rw [block_expansion X]
  simp only [tensorMap, Matrix.kronecker, krausMap, Fintype.sum_prod_type, Matrix.conjTranspose_kronecker,
    Matrix.mul_sum, Matrix.sum_mul, ← Matrix.mul_kronecker_mul,
    sum_kronecker, kronecker_sum]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
  exact sum_four_comm (fun (i j : Fin c) (k : r) (l : s) =>
    (Q k * Matrix.of (fun a b => X (a, i) (b, j)) * (Q k)ᴴ) ⊗ₖ
      (R l * Matrix.single i j 1 * (R l)ᴴ))

lemma krausMap_conjugate {r a b c d : Type*} [Fintype r] [Fintype a] [Fintype b]
    [Fintype c] (Q : r → Matrix b a ℂ) (U : Matrix a c ℂ) (V : Matrix d b ℂ)
    (A : Matrix c c ℂ) :
    V * krausMap Q (U * A * Uᴴ) * Vᴴ =
      krausMap (fun k => V * Q k * U) A := by
  simp only [krausMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

lemma krausMap_postconjugate {r a b c : Type*} [Fintype r] [Fintype a] [Fintype b]
    (Q : r → Matrix b a ℂ) (V : Matrix c b ℂ) (A : Matrix a a ℂ) :
    V * krausMap Q A * Vᴴ = krausMap (fun k => V * Q k) A := by
  simp only [krausMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

lemma krausMap_preconjugate {r a b c : Type*} [Fintype r] [Fintype a] [Fintype c]
    (Q : r → Matrix b a ℂ) (U : Matrix a c ℂ) (A : Matrix c c ℂ) :
    krausMap Q (U * A * Uᴴ) = krausMap (fun k => Q k * U) A := by
  simp only [krausMap, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
