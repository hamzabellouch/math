import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI

namespace SeymourSecondNeighborhood

open scoped BigOperators

section Evaluation

variable {σ ι K : Type*} [CommRing K] [IsDomain K] [Infinite K]

theorem exists_eval_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    ∃ a : σ → K, MvPolynomial.eval a p ≠ 0 := by
  classical
  by_contra h
  apply hp
  apply MvPolynomial.funext
  intro a
  have ha : MvPolynomial.eval a p = 0 := by
    by_contra ha
    exact h ⟨a, ha⟩
  simpa only [map_zero] using ha

theorem exists_eval_finset_ne_zero (s : Finset ι) (p : ι → MvPolynomial σ K)
    (hp : ∀ i ∈ s, p i ≠ 0) :
    ∃ a : σ → K, ∀ i ∈ s, MvPolynomial.eval a (p i) ≠ 0 := by
  classical
  have hprod : (∏ i ∈ s, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hprod
  refine ⟨a, ?_⟩
  have heval : (∏ i ∈ s, MvPolynomial.eval a (p i)) ≠ 0 := by
    simpa only [map_prod] using ha
  exact Finset.prod_ne_zero_iff.mp heval

theorem exists_eval_family_ne_zero [Fintype ι] (p : ι → MvPolynomial σ K)
    (hp : ∀ i, p i ≠ 0) :
    ∃ a : σ → K, ∀ i, MvPolynomial.eval a (p i) ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_eval_finset_ne_zero Finset.univ p (fun i _ => hp i)
  exact ⟨a, fun i => ha i (Finset.mem_univ i)⟩

end Evaluation

section Matrices

variable {σ K I J : Type*} [CommRing K]

noncomputable def evalPolynomialMatrix (a : σ → K) (M : Matrix I J (MvPolynomial σ K)) :
    Matrix I J K :=
  M.map (MvPolynomial.eval a)

@[simp] theorem evalPolynomialMatrix_apply (a : σ → K)
    (M : Matrix I J (MvPolynomial σ K)) (i : I) (j : J) :
    evalPolynomialMatrix a M i j = MvPolynomial.eval a (M i j) := rfl

@[simp] theorem evalPolynomialMatrix_submatrix {I' J' : Type*} (a : σ → K)
    (M : Matrix I J (MvPolynomial σ K)) (r : I' → I) (c : J' → J) :
    evalPolynomialMatrix a (M.submatrix r c) =
      (evalPolynomialMatrix a M).submatrix r c := rfl

@[simp] theorem det_evalPolynomialMatrix [Fintype I] [DecidableEq I]
    (a : σ → K) (M : Matrix I I (MvPolynomial σ K)) :
    (evalPolynomialMatrix a M).det = MvPolynomial.eval a M.det :=
  ((MvPolynomial.eval a).map_det M).symm

theorem det_ne_zero_of_evalPolynomialMatrix [Fintype I] [DecidableEq I]
    (a : σ → K) (M : Matrix I I (MvPolynomial σ K))
    (h : (evalPolynomialMatrix a M).det ≠ 0) : M.det ≠ 0 := by
  intro hz
  apply h
  simp only [det_evalPolynomialMatrix, hz, map_zero]

end Matrices

section SimultaneousDeterminants

variable {σ κ K : Type*} [CommRing K] [IsDomain K] [Infinite K] [Fintype κ]
variable {I : κ → Type*} [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]

theorem exists_simultaneous_det_ne_zero
    (M : ∀ k, Matrix (I k) (I k) (MvPolynomial σ K))
    (hM : ∀ k, (M k).det ≠ 0) :
    ∃ a : σ → K, ∀ k, (evalPolynomialMatrix a (M k)).det ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_eval_family_ne_zero (fun k => (M k).det) hM
  exact ⟨a, fun k => by simpa only [det_evalPolynomialMatrix] using ha k⟩

theorem exists_simultaneous_det_ne_zero_of_witness
    (M : ∀ k, Matrix (I k) (I k) (MvPolynomial σ K))
    (hM : ∀ k, ∃ a : σ → K, (evalPolynomialMatrix a (M k)).det ≠ 0) :
    ∃ a : σ → K, ∀ k, (evalPolynomialMatrix a (M k)).det ≠ 0 := by
  apply exists_simultaneous_det_ne_zero M
  intro k
  obtain ⟨a, ha⟩ := hM k
  exact det_ne_zero_of_evalPolynomialMatrix a (M k) ha

end SimultaneousDeterminants

section SimultaneousRanks

variable {σ κ K : Type*} [Field K] [Infinite K] [Fintype κ]
variable {I J : κ → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]

omit [(k : κ) → Fintype (I k)] in
theorem exists_simultaneous_rank_ge
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial σ K)) (n : κ → ℕ)
    (r : ∀ k, Fin (n k) → I k) (c : ∀ k, Fin (n k) → J k)
    (hminor : ∀ k, ((M k).submatrix (r k) (c k)).det ≠ 0) :
    ∃ a : σ → K, ∀ k, n k ≤ (evalPolynomialMatrix a (M k)).rank := by
  classical
  obtain ⟨a, ha⟩ := exists_simultaneous_det_ne_zero
    (fun k => (M k).submatrix (r k) (c k)) hminor
  refine ⟨a, fun k => ?_⟩
  have hdet : ((evalPolynomialMatrix a (M k)).submatrix (r k) (c k)).det ≠ 0 := by
    simpa only [evalPolynomialMatrix_submatrix] using ha k
  calc
    n k = ((evalPolynomialMatrix a (M k)).submatrix (r k) (c k)).rank := by
      simpa only [Fintype.card_fin] using (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ (evalPolynomialMatrix a (M k)).rank :=
      Matrix.rank_submatrix_le _ (r k) (c k)

omit [(k : κ) → Fintype (I k)] in
theorem exists_simultaneous_rank_eq
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial σ K)) (n : κ → ℕ)
    (r : ∀ k, Fin (n k) → I k) (c : ∀ k, Fin (n k) → J k)
    (hminor : ∀ k, ((M k).submatrix (r k) (c k)).det ≠ 0)
    (hupper : ∀ a : σ → K, ∀ k, (evalPolynomialMatrix a (M k)).rank ≤ n k) :
    ∃ a : σ → K, ∀ k, (evalPolynomialMatrix a (M k)).rank = n k := by
  obtain ⟨a, ha⟩ := exists_simultaneous_rank_ge M n r c hminor
  exact ⟨a, fun k => le_antisymm (hupper a k) (ha k)⟩

end SimultaneousRanks

end SeymourSecondNeighborhood

end OAI
