import OAI.Geometry.EinsteinFour.HessianTraceEquation
import OAI.Geometry.EinsteinFour.MatrixSlotCubic

namespace OAI

/-! The Weyl matrix equation in an arbitrary orthonormal frame. This
derivation uses the actual Bianchi Hessian and curvature commutator, so
no eigenframe is differentiated. -/

namespace PositiveEinsteinFour.TraceHessian

open scoped BigOperators
open Matrix
open HighestHessian

noncomputable section

def traceFreeSquare (M : Mat) : Mat :=
  M * M - (Matrix.trace (M * M) / 3) • (1 : Mat)

def weylLaplacian (M : Mat) : Mat := (6 : ℝ) • (M - traceFreeSquare M)

theorem traceFreeSquare_symmetric (M : Mat) (hs : symmetric M) :
    symmetric (traceFreeSquare M) := by
  have hm : Mᵀ = M := by ext a b; exact hs b a
  have hsq : (traceFreeSquare M)ᵀ = traceFreeSquare M := by
    simp only [traceFreeSquare, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_smul, Matrix.transpose_one, hm]
  intro a b
  exact congrArg (fun N : Mat => N b a) hsq

theorem traceFreeSquare_traceFree (M : Mat) : traceFree (traceFreeSquare M) := by
  change Matrix.trace (traceFreeSquare M) = 0
  simp only [traceFreeSquare, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, Nat.cast_ofNat]
  ring

theorem weylLaplacian_symmetric (M : Mat) (hs : symmetric M) :
    symmetric (weylLaplacian M) := by
  intro a b
  change 6 * (M a b - traceFreeSquare M a b) =
    6 * (M b a - traceFreeSquare M b a)
  rw [hs a b, traceFreeSquare_symmetric M hs a b]

theorem weylLaplacian_traceFree (M : Mat) (ht : traceFree M) :
    traceFree (weylLaplacian M) := by
  change (∑ a, 6 * (M a a - traceFreeSquare M a a)) = 0
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ht, traceFreeSquare_traceFree]
  ring

private theorem matrixAction_square_coordinates (a b c d e : ℝ) (r : Fin 3) :
    matrixAction r (traceFreeSquare (ofCoordinates a b c d e)) =
      -(∑ s, ofCoordinates a b c d e r s • matrixAction s (ofCoordinates a b c d e)) := by
  ext i j
  simp only [traceFreeSquare, matrixAction, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, smul_eq_mul]
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    norm_num [rotation, ofCoordinates, Matrix.one_apply, Fin.sum_univ_three] <;> ring

/-- The infinitesimal rotation of the trace-free square is computed
without a diagonalization hypothesis. -/
theorem matrixAction_traceFreeSquare (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (r : Fin 3) :
    matrixAction r (traceFreeSquare M) = -(∑ s, M r s • matrixAction s M) := by
  simpa only [coordinates_eq M hs ht] using
    matrixAction_square_coordinates (M 0 0) (M 1 1) (M 0 1) (M 0 2) (M 1 2) r

theorem matrixAction_weylLaplacian (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (r : Fin 3) :
    matrixAction r (weylLaplacian M) =
      (6 : ℝ) • (matrixAction r M + ∑ s, M r s • matrixAction s M) := by
  have hlin : matrixAction r (weylLaplacian M) =
      (6 : ℝ) • (matrixAction r M - matrixAction r (traceFreeSquare M)) := by
    ext a b
    simp only [weylLaplacian, matrixAction, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    ring_nf
  rw [hlin, matrixAction_traceFreeSquare M hs ht, sub_neg_eq_add]

/-- Curvature acting on the matrix bundle in the Ric=3g normalization.
The row `M r s` is the Weyl block in the same fixed frame. -/
def bundleCurvatureAction (M : Mat) (i j : Fin 4) (N : Mat) : Mat :=
  (1 / 2 : ℝ) • ∑ r, quaternionMatrix r i j •
    (matrixAction r N + ∑ s, M r s • matrixAction s N)

theorem traceComponent_weylLaplacian_skew (M : Mat)
    (hs : symmetric M) (ht : traceFree M) (i j : Fin 4) (a b : Fin 3) :
    traceComponent (weylLaplacian M) i j a b -
      traceComponent (weylLaplacian M) j i a b = bundleCurvatureAction M i j M a b := by
  rw [traceComponent_skew]
  have h (r : Fin 3) := congrArg (fun N : Mat => N a b)
    (matrixAction_weylLaplacian M hs ht r)
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  simp_rw [h]
  simp only [bundleCurvatureAction, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The full matrix Weyl equation is forced by differential Bianchi and
the classical curvature commutator. It holds in an arbitrary frame. -/
theorem weyl_trace_eq_of_bianchi_commutator (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0)
    (hc : ∀ i j a b, X i j a b - X j i a b = bundleCurvatureAction M i j M a b) :
    hessianTrace X = weylLaplacian M := by
  have hsB := weylLaplacian_symmetric M hs
  have htB := weylLaplacian_traceFree M ht
  have hY := HighestHessian.symmetric_bianchi_trace_zero (X - traceComponent (weylLaplacian M))
    (fun i j => by
      ext a b
      change X i j a b - traceComponent (weylLaplacian M) i j a b =
        X j i a b - traceComponent (weylLaplacian M) j i a b
      have h := hc i j a b
      have hk := traceComponent_weylLaplacian_skew M hs ht i j a b
      linarith)
    (fun i j a b => by
      change X i j a b - traceComponent (weylLaplacian M) i j a b =
        X i j b a - traceComponent (weylLaplacian M) i j b a
      rw [(hm i j).1 a b, traceComponent_symmetric _ hsB htB i j a b])
    (fun i r => by
      rw [divergence_sub, hb, traceComponent_divergence _ hsB htB, sub_self])
  unfold hessianTrace at hY
  change (∑ i, (X i i - traceComponent (weylLaplacian M) i i)) = 0 at hY
  rw [Finset.sum_sub_distrib] at hY
  change hessianTrace X - hessianTrace (traceComponent (weylLaplacian M)) = 0 at hY
  rw [trace_traceComponent] at hY
  exact sub_eq_zero.mp hY

end
end PositiveEinsteinFour.TraceHessian

end OAI
