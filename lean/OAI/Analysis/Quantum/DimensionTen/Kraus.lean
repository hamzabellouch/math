import OAI.Analysis.Quantum.DimensionTen.PencilModel

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder Kronecker
open Matrix
namespace DimensionTen

def krausMap {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) : Matrix b b ℂ :=
  ∑ k, Q k * A * (Q k)ᴴ

lemma krausMap_add {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A B : Matrix a a ℂ) :
    krausMap Q (A + B) = krausMap Q A + krausMap Q B := by
  simp [krausMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma krausMap_smul {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (c : ℂ) (A : Matrix a a ℂ) :
    krausMap Q (c • A) = c • krausMap Q A := by
  simp [krausMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma krausMap_linear {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) : IsComplexLinear (krausMap Q) :=
  ⟨krausMap_add Q, krausMap_smul Q⟩

lemma posSemidef_sum {r n : Type*} [Fintype r] (A : r → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i, A i).PosSemidef := by
  classical
  have hh : ∀ s : Finset r, (∑ i ∈ s, A i).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
    | @insert i s hi ih => simpa [Finset.sum_insert hi] using (h i).add ih
  exact hh Finset.univ

lemma krausMap_positive {r a b : Type*} [Fintype r] [Fintype a] [Finite b]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    (krausMap Q A).PosSemidef := by
  exact posSemidef_sum _ (fun k => hA.mul_mul_conjTranspose_same (Q k))

lemma krausMap_entry {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (u v : b) :
    krausMap Q A u v = ∑ k, ∑ i, ∑ j, Q k u i * A i j * star (Q k v j) := by
  simp only [krausMap, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]

lemma amplify_kraus {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (k : ℕ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    amplify (krausMap Q) k X = krausMap (fun r => (1 : Mat k) ⊗ₖ Q r) X := by
  ext u v
  change krausMap Q (fun i j => X (u.1, i) (v.1, j)) u.2 v.2 =
    krausMap (fun r => (1 : Mat k) ⊗ₖ Q r) X u v
  erw [krausMap_entry, krausMap_entry]
  have hentry (r : r) (u : Fin k × Fin b) (v : Fin k × Fin a) :
      ((1 : Mat k) ⊗ₖ Q r) u v = if u.1 = v.1 then Q r u.2 v.2 else 0 := by
    change (if u.1 = v.1 then (1 : ℂ) else 0) * Q r u.2 v.2 = _
    split <;> simp_all
  simp only [hentry]
  simp [Fintype.sum_prod_type, apply_ite star, ite_mul, mul_ite]

lemma krausMap_cp {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) : CompletelyPositive (krausMap Q) := by
  intro k hk X hX
  rw [amplify_kraus]
  exact krausMap_positive _ X hX

lemma krausMap_single {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (i j : Fin a) (u v : Fin b) :
    krausMap Q (Matrix.single i j 1) u v = ∑ k, Q k u i * star (Q k v j) := by
  simp [krausMap_entry, Matrix.single_apply, ite_and]

lemma krausMap_adjoint {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) :
    hsAdjoint (krausMap Q) = krausMap (fun k => (Q k)ᴴ) := by
  funext A
  ext i j
  change (∑ u, ∑ v, star (krausMap Q (Matrix.single i j 1) u v) * A u v) = _
  simp only [krausMap_single]
  simp only [krausMap_entry,
    star_sum, star_mul', star_star, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext v; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

end DimensionTen

end
end

end OAI
