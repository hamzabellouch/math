import OAI.Algebra.OddKaplansky.Augmentation

namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2

section

namespace OddKaplansky.Augmentation
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {E : Type portUniverse2} [Field K] [sectionInstance34 : Fintype E] [sectionInstance35 : DecidableEq E]
variable (p : ℕ) [sectionInstance36 : Fact p.Prime] [sectionInstance37 : CharP K p]

abbrev High (ell : ℕ) := {n : E → Fin p // Fintype.card E * (p-1) < ell + ∑ i, (n i).val}

def columns (ell : ℕ) : Matrix (C (E := E) p) (High (E := E) p ell) K :=
  fun x n => (monomial p n.val).coeff x

def regular : R (K := K) (E := E) p →ₐ[K] Matrix (C (E := E) p) (C (E := E) p) K :=
  Algebra.leftMulMatrix (MonoidAlgebra.basis _ K)

lemma basis_repr
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (z : R (K := K) (E := E) p) :
    (MonoidAlgebra.basis (C (E := E) p) K).repr z = z.coeff := rfl

lemma regular_delta
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (s : E → ZMod p) (x y : C (E := E) p) :
    regular (K := K) p (delta p s) x y = if x.toAdd = s + y.toAdd then 1 else 0 := by
  rw [regular, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [MonoidAlgebra.basis_apply, delta, MonoidAlgebra.single_mul_single, one_mul,
    basis_repr, MonoidAlgebra.coeff_single]
  simp only [Finsupp.single_apply, eq_comm]
  rfl

lemma regular_mul_vec
    {K : Type contextUniverse1}
    {E : Type contextUniverse2}
    [contextInstance2 : Field.{contextUniverse1} K]
    [Fintype.{contextUniverse2} E]
    [DecidableEq.{contextUniverse2 + 1} E]
    (p : Nat)
    [Fact (Nat.Prime p)]
    [@CharP.{contextUniverse1} K
  (@AddGroupWithOne.toAddMonoidWithOne.{contextUniverse1} K
    (@Ring.toAddGroupWithOne.{contextUniverse1} K (@DivisionRing.toRing.{contextUniverse1} K (@Field.toDivisionRing.{contextUniverse1} K contextInstance2))))
  p] (z t : R (K := K) (E := E) p) :
    regular p z *ᵥ (fun x => t.coeff x) = fun x => (z*t).coeff x := by
  have h := Algebra.leftMulMatrix_mulVec_repr (MonoidAlgebra.basis (C (E := E) p) K) z t
  simpa only [regular, basis_repr] using h

lemma columns_independent (ell : ℕ) : LinearIndependent K (columns (K := K) (E := E) p ell).col := by
  let L : R (K := K) (E := E) p ≃ₗ[K] (C (E := E) p → K) :=
    (MonoidAlgebra.coeffLinearEquiv K).trans (Finsupp.linearEquivFunOnFinite K K (C p))
  have h := ((monomial_independent (K := K) (E := E) p).comp (fun n : High (E := E) p ell => n.val) Subtype.val_injective).map' L.toLinearMap L.ker
  exact h

lemma columns_annihilated (ell : ℕ) (s : E → ZMod p) :
    (regular (K := K) p (delta p s) - 1)^ell * columns (K := K) (E := E) p ell = 0 := by
  have he : (regular (K := K) p (delta p s) - 1)^ell = regular p ((delta p s - 1)^ell) := by simp
  rw [he]
  ext x n
  change (regular p ((delta p s - 1)^ell) *ᵥ (fun x => (monomial p n.val).coeff x)) x = 0
  rw [regular_mul_vec, annihilates_monomial p s n.val ell n.property]
  rfl

lemma regular_delta_transpose (s : E → ZMod p) :
    (regular (K := K) p (delta p s)).transpose = regular p (delta p (-s)) := by
  ext x y
  simp only [Matrix.transpose_apply,regular_delta]
  congr 1
  apply propext
  constructor
  · intro h; rw [h]; simp
  · intro h; rw [h]; simp

lemma columns_transpose_annihilated (ell : ℕ) (s : E → ZMod p) :
    (columns (K := K) (E := E) p ell).transpose * (regular (K := K) (E := E) p (delta p s)-(1 : Matrix (C p) (C p) K))^ell = 0 := by
  have h := congrArg Matrix.transpose (columns_annihilated (K := K) (E := E) p ell (-s))
  simpa only [Matrix.transpose_mul, Matrix.transpose_pow, Matrix.transpose_sub,
    Matrix.transpose_one, regular_delta_transpose, neg_neg, Matrix.transpose_zero] using h

end
end OddKaplansky.Augmentation

end

end OAI
