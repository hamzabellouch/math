import OAI.Analysis.WeakInfiniteness.ChoiFactor

namespace OAI

/-! Choi square-root coefficients preserve an external commutant. This is the
finite matrix positivity step for the commuting tensor functional in KR02 7.18. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

local instance commutingChoiRealModule {n : Type*} [Fintype n] :
    Module ℝ (CStarMatrix n n D) := Module.complexToReal _

omit [PartialOrder D] [StarOrderedRing D] in
lemma matrix_commute_diagonal_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M : CStarMatrix n n D) (d : D) :
    Commute M (matrixDiagonalHom (n := n) d) ↔ ∀ i j, Commute (M i j) d := by
  constructor
  · intro h i j
    change M i j * d = d * M i j
    have he := congrArg (fun X : CStarMatrix n n D => X i j) h.eq
    change ((CStarMatrix.ofMatrix.symm M) * Matrix.diagonal (fun _ : n => d)) i j =
      (Matrix.diagonal (fun _ : n => d) * (CStarMatrix.ofMatrix.symm M)) i j at he
    simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, CStarMatrix.ofMatrix_symm_apply] using he
  · intro h
    apply Commute.symm
    change _ * _ = _ * _
    ext i j
    change (Matrix.diagonal (fun _ : n => d) * CStarMatrix.ofMatrix.symm M) i j =
      (CStarMatrix.ofMatrix.symm M * Matrix.diagonal (fun _ : n => d)) i j
    simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, CStarMatrix.ofMatrix_symm_apply] using (h i j).eq.symm

theorem completelyPositive_matrix_gram_commuting {n : ℕ} (hn : 1 ≤ n)
    (ψ : CStarMatrix (Fin n) (Fin n) ℂ →L[ℂ] D) (hψ : CompletelyPositive ψ)
    {C : Type*} (y : C → D) (hc : ∀ i j c, Commute (ψ (matrixUnit i j)) (y c)) :
    ∃ X : CStarMatrix (Fin n) (Fin n) D,
      (∀ i j, ψ (matrixUnit i j) = ∑ k, star (X k i) * X k j) ∧
      ∀ i j c, Commute (X i j) (y c) := by
  let M : CStarMatrix (Fin n) (Fin n) D :=
    matrixLinearMap ψ (CStarMatrix.ofMatrix (fun i j => matrixUnit i j))
  have hM : 0 ≤ M := matrixLinearMap_nonneg hψ
    (matrixUnits_nonneg (⟨0, by omega⟩ : Fin n))
  let X := CFC.sqrt M
  have he : star X * X = M := by
    rw [(CFC.sqrt_nonneg M).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self M hM
  refine ⟨X, fun i j => (congrArg (fun Q : CStarMatrix (Fin n) (Fin n) D => Q i j) he).symm, ?_⟩
  intro i j c
  have hm : Commute M (matrixDiagonalHom (n := Fin n) (y c)) :=
    (matrix_commute_diagonal_iff M (y c)).mpr (fun i j => hc i j c)
  have hx : Commute X (matrixDiagonalHom (n := Fin n) (y c)) :=
    hm.cfcₙ_nnreal NNReal.sqrt
  exact (matrix_commute_diagonal_iff X (y c)).mp hx i j

end WeakPureInfiniteness

end

end OAI
