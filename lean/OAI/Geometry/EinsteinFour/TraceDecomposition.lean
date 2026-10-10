import OAI.Geometry.EinsteinFour.TraceCurvature
import OAI.Geometry.EinsteinFour.HighestHessian

namespace OAI

/-! The actual local tensor identities imply the highest-Hessian constraints. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem matrixAction_symmetric (s : Fin 3) (M : Mat)
    (hs : symmetric M) (ht : traceFree M) : symmetric (matrixAction s M) := by
  rw [← coordinates_eq M hs ht]
  intro a b
  fin_cases s <;> fin_cases a <;> fin_cases b <;>
    simp [matrixAction, rotation, ofCoordinates, Fin.sum_univ_succ]
  all_goals ring

private theorem matrixAction_traceFree (s : Fin 3) (M : Mat)
    (hs : symmetric M) (ht : traceFree M) : traceFree (matrixAction s M) := by
  rw [← coordinates_eq M hs ht]
  fin_cases s <;> simp [traceFree, matrixAction, rotation, ofCoordinates, Fin.sum_univ_succ]

theorem traceComponent_symmetric (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (i j : Fin 4) : symmetric (traceComponent M i j) := by
  intro a b
  have h (s : Fin 3) : matrixAction s M a b = matrixAction s M b a :=
    matrixAction_symmetric s M hs ht a b
  change (5 / 12 : ℝ) * traceLift M i j a b =
    (5 / 12 : ℝ) * traceLift M i j b a
  simp only [traceLift, h, hs a b]

theorem traceComponent_traceFree (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (i j : Fin 4) : traceFree (traceComponent M i j) := by
  have h (s : Fin 3) : (∑ a, matrixAction s M a a) = 0 :=
    matrixAction_traceFree s M hs ht
  have hdiag : (∑ a : Fin 3, if i = j then (3 / 5 : ℝ) * M a a else 0) = 0 := by
    by_cases hij : i = j
    · simp only [hij, ite_true, ← Finset.mul_sum]
      rw [show (∑ a, M a a) = 0 from ht, mul_zero]
    · simp [hij]
  change (∑ a, (5 / 12 : ℝ) * traceLift M i j a a) = 0
  simp only [← Finset.mul_sum, traceLift, Finset.sum_add_distrib]
  rw [hdiag, zero_add]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, h, mul_zero, Finset.sum_const_zero]

theorem divergence_add (X Y : Hessian) (i : Fin 4) (r : Fin 3) :
    divergence (X + Y) i r = divergence X i r + divergence Y i r := by
  have h (s : Fin 3) :
      WithLp.toLp 2 (fun j => (X + Y) i j s r) =
        WithLp.toLp 2 (fun j => X i j s r) + WithLp.toLp 2 (fun j => Y i j s r) := rfl
  simp only [divergence, h, quaternion_add, Finset.sum_add_distrib]

theorem divergence_smul (a : ℝ) (X : Hessian) (i : Fin 4) (r : Fin 3) :
    divergence (a • X) i r = a • divergence X i r := by
  have h (s : Fin 3) :
      WithLp.toLp 2 (fun j => (a • X) i j s r) =
        a • WithLp.toLp 2 (fun j => X i j s r) := rfl
  simp only [divergence, h, quaternion_smul, Finset.smul_sum]

theorem divergence_sub (X Y : Hessian) (i : Fin 4) (r : Fin 3) :
    divergence (X - Y) i r = divergence X i r - divergence Y i r := by
  rw [sub_eq_add_neg, divergence_add]
  have h : divergence (-Y) i r = -divergence Y i r := by
    simpa only [neg_one_smul] using divergence_smul (-1) Y i r
  rw [h, sub_eq_add_neg]

theorem traceComponent_divergence (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (i : Fin 4) (r : Fin 3) : divergence (traceComponent M) i r = 0 := by
  change divergence ((5 / 12 : ℝ) • traceLift M) i r = 0
  rw [divergence_smul]
  change (5 / 12 : ℝ) • liftDivergence M i r = 0
  rw [traceLift_bianchi M hs ht, smul_zero]

/-- No representation-theoretic hypothesis is needed: matrix symmetry,
the actual trace equation, Bianchi and the curvature commutator suffice. -/
theorem trace_subtracted_condition (X : Hessian) (t : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (htrace : hessianTrace X = diagonalLaplacianBlock t)
    (hbianchi : ∀ i r, divergence X i r = 0)
    (hcomm : ∀ i j a b, X i j a b - X j i a b =
      (1 / 2) * ∑ s, (1 + t s) * quaternionMatrix s i j *
        matrixAction s (Matrix.diagonal t) a b) :
    condition (X - traceComponent (diagonalLaplacianBlock t)) := by
  have hsM : symmetric (diagonalLaplacianBlock t) := by
    intro a b
    by_cases h : a = b
    · subst b
      rfl
    · simp [diagonalLaplacianBlock, Matrix.diagonal, h, Ne.symm h]
  have htM : traceFree (diagonalLaplacianBlock t) := by
    have ht' := ht
    simp [Fin.sum_univ_succ] at ht'
    simp [traceFree, diagonalLaplacianBlock, Matrix.diagonal, Fin.sum_univ_succ]
    nlinarith
  refine ⟨trace_subtracted_symmetric X t ht hcomm, ?_, ?_, ?_⟩
  · intro i j
    constructor
    · intro a b
      change X i j a b - traceComponent (diagonalLaplacianBlock t) i j a b =
        X i j b a - traceComponent (diagonalLaplacianBlock t) i j b a
      rw [(hm i j).1 a b, traceComponent_symmetric _ hsM htM i j a b]
    · change (∑ a : Fin 3,
        (X i j a a - traceComponent (diagonalLaplacianBlock t) i j a a)) = 0
      rw [Finset.sum_sub_distrib, (hm i j).2,
        traceComponent_traceFree _ hsM htM i j, sub_self]
  · unfold hessianTrace
    change (∑ i : Fin 4, (X i i - traceComponent (diagonalLaplacianBlock t) i i)) = 0
    rw [Finset.sum_sub_distrib]
    change hessianTrace X - hessianTrace (traceComponent (diagonalLaplacianBlock t)) = 0
    rw [htrace, trace_traceComponent, sub_self]
  · intro i r
    rw [divergence_sub, hbianchi, traceComponent_divergence _ hsM htM, sub_self]

end
end PositiveEinsteinFour.HighestHessian

end OAI
