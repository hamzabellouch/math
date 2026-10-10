import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathsCalibration

namespace OAI

/-! Explicit ordinary-spin edges for simultaneous path subdivisions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaPathOffset (J : ℝ) : ℝ := 3/4+3*J^2

theorem qmaPathsBase_matrix {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant R : ℝ) (J : Fin r → ℝ) :
    qmaExchangeMatrix left right weight (constant+∑ e, qmaPathOffset (J e)) =
      qmaExchangeMatrix left right weight constant +
        ∑ e, qmaPathCorrection (n := n) R (J e) := by
  simp only [qmaExchangeMatrix,qmaPathCorrection,qmaPathOffset,
    Complex.ofReal_add,Complex.ofReal_sum,add_smul,Finset.sum_smul]
  abel

def qmaPathsGraph {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant R : ℝ) (site : Fin r → Fin 2 → Fin n) (even : Fin r → Bool) (J : Fin r → ℝ) :
    Matrix (SourceSpinBasis (n+r*2)) (SourceSpinBasis (n+r*2)) ℂ :=
  qmaExchangeMatrix
    (qmaParallelGraphLeft left site)
    (qmaParallelGraphRight right (fun e => qmaPathMember (even e)))
    (qmaParallelGraphWeight weight (R^2) (fun e => qmaPathAmplitude (even e) R (J e)))
    ((constant+∑ e, qmaPathOffset (J e))+3*r*(R^2))

theorem qmaPathsGraph_matrix {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant R : ℝ)
    (site : Fin r → Fin 2 → Fin n) (even : Fin r → Bool) (J : Fin r → ℝ) :
    (qmaPathsGraph left right weight constant R site even J).submatrix
      (basisEquiv n r) (basisEquiv n r) =
      qmaPhysicalParallelHamiltonian n r (R^2)
        (qmaExchangeMatrix left right weight constant+∑ e, qmaPathCorrection (n := n) R (J e))
        site (fun e => qmaPathMember (even e)) (fun e => qmaPathAmplitude (even e) R (J e)) := by
  unfold qmaPathsGraph
  have h := qmaParallelGraph_matrix left right hneq weight
      (constant+∑ e, qmaPathOffset (J e)) (R^2)
      site (fun e => qmaPathMember (even e)) (fun e => qmaPathAmplitude (even e) R (J e))
  rw [qmaPathsBase_matrix left right weight constant R J] at h
  exact h

theorem qmaPathsGraph_accuracy {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ)
    (site : Fin r → Fin 2 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (even : Fin r → Bool) (J : Fin r → ℝ) {N : ℝ} (hN : 0 < N) :
    let B := 3*(∑ a, |weight a|)+|constant|
    let A := 3*∑ e, (1+2*|J e|)
    let D := B+4*∑ e, (1+|J e|)^2
    let R := qmaRoutingScale A D N
    |sourceMatrixBottom (n+r*2) (qmaPathsGraph left right weight constant R site even J) -
      sourceMatrixBottom n (qmaExchangeMatrix left right weight constant + ∑ e,
        (J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1))| ≤ 1/N := by
  dsimp only
  rw [sourceMatrixBottom_eq_mediator n r,qmaPathsGraph_matrix left right hneq weight constant,
    qmaPhysicalParallel_bottom]
  have hC : (qmaExchangeMatrix left right weight constant).conjTranspose =
      qmaExchangeMatrix left right weight constant := by
    simp only [qmaExchangeMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul,sourceHeisenbergMatrix_star n _ _ (hneq _),
      Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_one]
  exact qmaPaths_accuracy site hsite even J (by positivity) hN _ hC
    (qmaExchangeMatrix_lift_norm left right hneq weight constant)

end ContinuumCoulomb

end

end OAI
