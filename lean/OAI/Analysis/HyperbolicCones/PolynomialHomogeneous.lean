import OAI.Analysis.HyperbolicCones.Model

namespace OAI

noncomputable section

open Matrix MvPolynomial
open scoped BigOperators

universe u v

namespace Paper256

theorem determinant_homogeneous {ι : Type u} {σ : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℝ)) (d : ℕ)
    (hM : ∀ i j, (M i j).IsHomogeneous d) :
    M.det.IsHomogeneous (Fintype.card ι * d) := by
  classical
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro p _
  have hp : (∏ i, M (p i) i).IsHomogeneous (Fintype.card ι * d) := by
    simpa using IsHomogeneous.prod Finset.univ (fun i => M (p i) i)
      (fun _ => d) (fun i _ => hM (p i) i)
  simpa using hp.C_mul ((Equiv.Perm.sign p : ℤ) : ℝ)

theorem adjugate_homogeneous {σ : Type u} {n : ℕ}
    (M : Mat (n + 1) (MvPolynomial σ ℝ)) (d : ℕ)
    (hM : ∀ i j, (M i j).IsHomogeneous d) (i j : Fin (n + 1)) :
    (M.adjugate i j).IsHomogeneous (n * d) := by
  classical
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hc : ((-1 : MvPolynomial σ ℝ) ^ (j.val + i.val)).IsHomogeneous 0 := by
    simpa using (isHomogeneous_one (σ := σ) (R := ℝ)).neg.pow (j.val + i.val)
  have hm := determinant_homogeneous (M.submatrix j.succAbove i.succAbove) d
    (fun a b => hM (j.succAbove a) (i.succAbove b))
  simpa using hc.mul hm

theorem qMatrix_homogeneous {σ : Type u} (y : Fin 3 → MvPolynomial σ ℝ)
    (hy : ∀ i, (y i).IsHomogeneous 1) (i j : Fin 3) :
    (qMatrix y i j).IsHomogeneous 2 := by
  classical
  by_cases h : i = j
  · simpa [qMatrix, h] using ((hy i).pow 2).add ((hy (i + 1)).pow 2)
  · simpa [qMatrix, h] using ((hy i).mul (hy j)).neg

theorem phi_homogeneous {σ : Type u} (y : Fin 3 → MvPolynomial σ ℝ)
    (M : Mat 4 (MvPolynomial σ ℝ))
    (hy : ∀ i, (y i).IsHomogeneous 1)
    (hM : ∀ i j, (M i j).IsHomogeneous 3) (i j : Fin 4) :
    (phi y M i j).IsHomogeneous 5 := by
  classical
  have hq := qMatrix_homogeneous y hy
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [phi, Fin.cases_zero, Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Matrix.submatrix_apply]
      apply IsHomogeneous.sum
      intro a _
      apply IsHomogeneous.sum
      intro b _
      exact (hq a b).mul (hM b.succ a.succ)
    · simp only [phi, Fin.cases_zero, Fin.cases_succ]
      apply IsHomogeneous.neg
      apply IsHomogeneous.sum
      intro a _
      exact (hM 0 a.succ).mul (hq a j)
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [phi, Fin.cases_succ, Fin.cases_zero]
      apply IsHomogeneous.neg
      apply IsHomogeneous.sum
      intro a _
      exact (hq i a).mul (hM a.succ 0)
    · simp only [phi, Fin.cases_succ]
      exact (hM 0 0).mul (hq i j)

theorem polynomial_homogeneous : polynomial.IsHomogeneous 20 := by
  classical
  let X : Mat 4 (MvPolynomial Coord ℝ) :=
    symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij))
  let Z : Mat 4 (MvPolynomial Coord ℝ) :=
    symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inr ij))
  let y : Fin 3 → MvPolynomial Coord ℝ := fun i => MvPolynomial.X (Sum.inr i)
  have hX : ∀ i j, (X i j).IsHomogeneous 1 := by
    intro i j
    dsimp [X, symmetricCoordinates]
    split <;> exact isHomogeneous_X _ _
  have hZ : ∀ i j, (Z i j).IsHomogeneous 1 := by
    intro i j
    dsimp [Z, symmetricCoordinates]
    split <;> exact isHomogeneous_X _ _
  have hy : ∀ i, (y i).IsHomogeneous 1 := fun i => isHomogeneous_X _ _
  have hd : X.det.IsHomogeneous 4 := by
    simpa using determinant_homogeneous X 1 hX
  have ha : ∀ i j, (X.adjugate i j).IsHomogeneous 3 := by
    intro i j
    simpa using adjugate_homogeneous X 1 hX i j
  have hp := phi_homogeneous y X.adjugate hy ha
  have hm : ∀ i j, (((X.det) • Z - phi y X.adjugate) i j).IsHomogeneous 5 := by
    intro i j
    exact (hd.mul (hZ i j)).sub (hp i j)
  simpa [polynomial, matrixValue, X, Z, y] using
    determinant_homogeneous ((X.det) • Z - phi y X.adjugate) 5 hm

end Paper256

end

end OAI
