import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialWitnessProduct
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialExecutionSymmetry

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.MatrixBalancing

open MatrixMultiplication.Foundation
open MatrixMultiplication.Foundation.Tensor

variable {K X Y Z : Type*} [Field K]
variable {r d D : ℕ}

def swapXYApproximation {T : Tensor K X Y Z}
    (P : PolynomialApproximation T r d D) :
    PolynomialApproximation (Tensor.swapXY T) r d D where
  polynomial := Tensor.swapXY P.polynomial
  rank_bound := P.rank_bound.swapXY
  vanishes := fun y x z k hk => P.vanishes x y z k hk
  leading := fun y x z => P.leading x y z
  degree_bound := fun y x z => P.degree_bound x y z

private theorem swapXY_directSum {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    Tensor.swapXY (Tensor.directSum T) =
      Tensor.directSum (fun i => Tensor.swapXY (T i)) := by
  funext x y z
  have hguard : (y.1 = x.1 ∧ y.1 = z.1) ↔ (x.1 = y.1 ∧ x.1 = z.1) := by
    constructor
    · rintro ⟨hyx, hyz⟩
      exact ⟨hyx.symm, hyx.symm.trans hyz⟩
    · rintro ⟨hxy, hxz⟩
      exact ⟨hxy.symm, hxy.symm.trans hxz⟩
  simp only [Tensor.swapXY, Tensor.directSum, hguard]
  split_ifs with h
  · rw [h.1]
  · rfl

def directSum_swapXY {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z}
    (P : PolynomialApproximation (Tensor.directSum T) r d D) :
    PolynomialApproximation (Tensor.directSum (fun i => Tensor.swapXY (T i))) r d D := by
  simpa only [swapXY_directSum] using swapXYApproximation P

section Matrix

variable {ι A B C : Type*} [DecidableEq ι]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrix_swapYZ :
    Tensor.pullback (Prod.swap : B × A → A × B)
      (Prod.swap : A × C → C × A) (Prod.swap : C × B → B × C)
      (Tensor.cyclic (Tensor.swapXY (matrixCoefficients (K := K) A B C))) =
        matrixCoefficients (K := K) B A C := by
  funext x y z
  simp only [Tensor.pullback, Tensor.cyclic, Tensor.swapXY, Prod.swap,
    matrixCoefficients]
  simp only [eq_comm, and_comm, and_left_comm]

theorem matrix_swapXZ :
    Tensor.pullback (Prod.swap : A × C → C × A)
      (Prod.swap : C × B → B × C) (Prod.swap : B × A → A × B)
      (Tensor.swapXY (Tensor.cyclic (matrixCoefficients (K := K) A B C))) =
        matrixCoefficients (K := K) A C B := by
  funext x y z
  simp only [Tensor.pullback, Tensor.cyclic, Tensor.swapXY, Prod.swap,
    matrixCoefficients]
  simp only [eq_comm, and_comm, and_left_comm, and_assoc]

def matrixDirectSum_swapYZ
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) B A C)) r d D := by
  have h := (directSum_swapXY P).directSum_cyclic.directSum_pullback
    (Prod.swap : B × A → A × B) (Prod.swap : A × C → C × A)
    (Prod.swap : C × B → B × C)
  simpa only [matrix_swapYZ] using h

def matrixDirectSum_swapXZ
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A C B)) r d D := by
  have h := (directSum_swapXY P.directSum_cyclic).directSum_pullback
    (Prod.swap : A × C → C × A) (Prod.swap : C × B → B × C)
    (Prod.swap : B × A → A × B)
  simpa only [matrix_swapXZ] using h

def matrixDirectSum_reindex {κ A' B' C' : Type*}
    [DecidableEq κ] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D)
    (e : κ → ι) (he : Function.Injective e)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : κ => matrixCoefficients (K := K) A' B' C')) r d D := by
  have h := P.pullback
    (fun x : κ × (A' × B') => (e x.1, (f x.2.1, g x.2.2)))
    (fun y : κ × (B' × C') => (e y.1, (g y.2.1, j y.2.2)))
    (fun z : κ × (C' × A') => (e z.1, (j z.2.1, f z.2.2)))
  convert h using 1
  funext x y z
  simp only [Tensor.pullback, Tensor.directSum, matrixCoefficients,
    he.eq_iff, hf.eq_iff, hg.eq_iff, hj.eq_iff]

def matrixDirectSum_product {κ A' B' C' : Type*}
    [DecidableEq κ] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    {s e E : ℕ}
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D)
    (Q : PolynomialApproximation
      (Tensor.directSum (fun _ : κ => matrixCoefficients (K := K) A' B' C')) s e E) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : ι × κ =>
        matrixCoefficients (K := K) (A × A') (B × B') (C × C')))
      (r * s) (d + e) (D + E) := by
  have h := (P.directSum_product Q).directSum_pullback
    (fun x : (A × A') × (B × B') => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × B') × (C × C') => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × C') × (A × A') => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
  convert h using 1
  funext x y z
  simp only [Tensor.directSum, Tensor.pullback, matrixCoefficients_product]

def matrixDirectSum_balanced
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : ι × ι =>
        matrixCoefficients (K := K) (A × B) (C × C) (A × B)))
      (r ^ 2) (2 * d) (2 * D) := by
  have h := matrixDirectSum_swapXZ (matrixDirectSum_product P (matrixDirectSum_swapYZ P))
  have h' := matrixDirectSum_reindex h
    (Equiv.refl (ι × ι)) (Equiv.refl _).injective
    (Equiv.refl (A × B)) (Equiv.refl _).injective
    (Equiv.refl (C × C)) (Equiv.refl _).injective
    (Equiv.prodComm A B) (Equiv.prodComm A B).injective
  simpa only [pow_two, two_mul] using h'

end Matrix

def finiteBalanced {L a b c : ℕ}
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : Fin L =>
        matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : Fin (L ^ 2) =>
        matrixCoefficients (K := K) (Fin (a * b)) (Fin (c ^ 2)) (Fin (a * b))))
      (r ^ 2) (2 * d) (2 * D) := by
  let tags : Fin (L ^ 2) ≃ Fin L × Fin L := Fintype.equivOfCardEq (by simp [pow_two])
  let outer : Fin (a * b) ≃ Fin a × Fin b := Fintype.equivOfCardEq (by simp)
  let inner : Fin (c ^ 2) ≃ Fin c × Fin c := Fintype.equivOfCardEq (by simp [pow_two])
  exact matrixDirectSum_reindex (matrixDirectSum_balanced P)
    tags tags.injective outer outer.injective inner inner.injective outer outer.injective

end MatrixMultiplication.MatrixBalancing

end

end OAI
