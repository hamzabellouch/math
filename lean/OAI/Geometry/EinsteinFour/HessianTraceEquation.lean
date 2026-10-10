import OAI.Geometry.EinsteinFour.BianchiSlices
import OAI.Geometry.EinsteinFour.WeightedHessian
import OAI.Geometry.EinsteinFour.GradientCasimir

namespace OAI

/-! Derive the Weyl Hessian trace from Bianchi and the curvature commutator.
This removes a separate tensor Laplacian premise from the local weighted
square. All contractions use the same concrete quaternion coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem rotation_innerSlice_component (X : Hessian)
    (hs : ∀ i j, symmetric (X i j)) (s : Fin 3) (i k : Fin 4) (a b : Fin 3) :
    matrixRotation s (innerSlice X i) a b k = matrixAction s (X i k) a b := by
  simp only [matrixRotation, innerSlice_matrix X i (hs i), matrixAction]
  simp [Fin.sum_univ_three]
  ring

private theorem coupling_innerSlice_component (X : Hessian)
    (hs : ∀ i j, symmetric (X i j))
    (hb : ∀ i r, divergence X i r = 0) (i j : Fin 4) (a b : Fin 3) :
    (∑ s, ∑ k, quaternionMatrix s j k * matrixAction s (X i k) a b) =
      -4 * X i j a b := by
  have h := congrArg (fun v : Vec => v j)
    (gradientCoupling_eq (innerSlice X i) (innerSlice_bianchi X i (hs i) (hb i)) a b)
  simp only [gradientCoupling, WithLp.ofLp_sum, Finset.sum_apply] at h
  simp_rw [← quaternionMatrix_apply, rotation_innerSlice_component X hs] at h
  simpa only [innerSlice_matrix X i (hs i), PiLp.smul_apply, smul_eq_mul] using h

/-- A derivative-symmetric Bianchi Hessian has zero trace. -/
theorem symmetric_bianchi_trace_zero (X : Hessian)
    (hderiv : ∀ i j, X i j = X j i)
    (hs : ∀ i j, symmetric (X i j))
    (hb : ∀ i r, divergence X i r = 0) : hessianTrace X = 0 := by
  ext a b
  have hskew (s : Fin 3) :
      (∑ i, ∑ k, quaternionMatrix s i k * matrixAction s (X i k) a b) = 0 := by
    have he :
        (∑ i, ∑ k, quaternionMatrix s i k * matrixAction s (X i k) a b) =
        -(∑ i, ∑ k, quaternionMatrix s i k * matrixAction s (X i k) a b) := by
      calc
        _ = ∑ k, ∑ i, quaternionMatrix s i k * matrixAction s (X i k) a b :=
          Finset.sum_comm
        _ = _ := by
          simp only [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          rw [quaternionMatrix_skew s k i, hderiv k i]
          ring
    linarith
  have he : (∑ i, ∑ s, ∑ k,
      quaternionMatrix s i k * matrixAction s (X i k) a b) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [hskew]
    simp
  simp_rw [coupling_innerSlice_component X hs hb] at he
  simp only [← Finset.mul_sum] at he
  change (∑ i, X i i a b) = 0
  linarith

/-- The normalized Weyl trace equation is a consequence of the local
curvature commutator and differential Bianchi identity. -/
theorem trace_eq_of_bianchi_commutator (X : Hessian) (t : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0)
    (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0)
    (hc : ∀ i j a b, X i j a b - X j i a b =
      (1 / 2) * ∑ s, (1 + t s) * quaternionMatrix s i j *
        matrixAction s (Matrix.diagonal t) a b) :
    hessianTrace X = diagonalLaplacianBlock t := by
  have hsD : symmetric (diagonalLaplacianBlock t) := by
    intro a b
    by_cases h : a = b
    · subst b
      rfl
    · simp [diagonalLaplacianBlock, Matrix.diagonal, h, Ne.symm h]
  have htD : traceFree (diagonalLaplacianBlock t) := by
    have h := ht
    simp only [Fin.sum_univ_three] at h
    simp [traceFree, diagonalLaplacianBlock, Matrix.diagonal, Fin.sum_univ_three]
    linarith
  have hY := symmetric_bianchi_trace_zero
    (X - traceComponent (diagonalLaplacianBlock t))
    (trace_subtracted_symmetric X t ht hc)
    (fun i j a b => by
      change X i j a b - traceComponent (diagonalLaplacianBlock t) i j a b =
        X i j b a - traceComponent (diagonalLaplacianBlock t) i j b a
      rw [(hm i j).1 a b, traceComponent_symmetric _ hsD htD i j a b])
    (fun i r => by
      rw [divergence_sub, hb, traceComponent_divergence _ hsD htD, sub_self])
  unfold hessianTrace at hY
  change (∑ i, (X i i - traceComponent (diagonalLaplacianBlock t) i i)) = 0 at hY
  rw [Finset.sum_sub_distrib] at hY
  change hessianTrace X - hessianTrace (traceComponent (diagonalLaplacianBlock t)) = 0 at hY
  rw [trace_traceComponent] at hY
  exact sub_eq_zero.mp hY

/-- The local weighted square needs no independent Laplacian equation. -/
theorem local_weighted_hessian_square_of_bianchi_commutator
    (X : Hessian) (t u : Fin 3 → ℝ) (a : Vec) (Z : Tensor)
    (ht : ∑ s, t s = 0)
    (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0)
    (hcomm : ∀ i j b c, X i j b c - X j i b c =
      (1 / 2) * ∑ s, (1 + t s) * quaternionMatrix s i j *
        matrixAction s (Matrix.diagonal t) b c)
    (x y m : ℝ) (hm : 0 < m)
    (htx : ∀ s, -x ≤ t s) (huy : ∀ s, -y ≤ u s) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * curvaturePairing t u (hessianRemainder X t) (hessianRemainder X t) +
      curvaturePairing t u (hessianRemainder X t) (weightTensor a Z) / 6 +
      curvaturePairing t u (highestProjection (weightTensor a Z))
        (highestProjection (weightTensor a Z)) / (24 * m) :=
  local_weighted_hessian_square X t u a Z ht hmatrix
    (trace_eq_of_bianchi_commutator X t ht hmatrix hbianchi hcomm)
    hbianchi hcomm x y m hm htx huy hxy

end

end PositiveEinsteinFour.HighestHessian

end OAI
