import OAI.NumberTheory.Ostmann.Quadratic.KernelCoordinateIdentity
import OAI.NumberTheory.Ostmann.Characters.SparsePolydiscBlocks

namespace OAI

/-! # Exact polynomial kernel entries in centered residue coordinates -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

private noncomputable def localPairing {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) : ℂ :=
  ∑ x, conj (f x) * g x

private theorem localPairing_left {p : ℕ} [NeZero p]
    (f g h : ZMod p → ℂ) (c d : ℂ) :
    localPairing (fun x => c * f x + d * g x) h =
      conj c * localPairing f h + conj d * localPairing g h := by
  unfold localPairing
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [map_add, map_mul]
  ring

private theorem localPairing_right {p : ℕ} [NeZero p]
    (f g h : ZMod p → ℂ) (c d : ℂ) :
    localPairing f (fun x => c * g x + d * h x) =
      c * localPairing f g + d * localPairing f h := by
  unfold localPairing
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The matrix bounded on the polydisc has precisely the desired entries
`(1+u*b(a-b))*(1+v*b(a-b))`, including its constant mode. -/
theorem polynomial_kernel_coordinate_identity {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ Finset.univ \ S)
    (u v : ℂ) :
    (1 + u * localSparseKernel E (a - b)) * (1 + v * localSparseKernel E (a - b)) =
      polydiscSparseScalar S E (u + v) (u * v) +
      (∑ x, conj (polydiscSparseSide (Finset.univ \ S) S E (conj (u + v)) (conj (u * v)) x) *
        centeredSupportProjection (Finset.univ \ S) (residuePointVector b) x) +
      (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
        polydiscSparseSide S (Finset.univ \ S) E (u + v) (u * v) x) +
      (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
        polydiscSparseLower S (Finset.univ \ S) E (u + v) (u * v)
          (centeredSupportProjection (Finset.univ \ S) (residuePointVector b)) x) := by
  let T := Finset.univ \ S
  let A := centeredSupportProjection S (residuePointVector a)
  let B := centeredSupportProjection T (residuePointVector b)
  let k := localSparseKernel E
  let k₂ := localSparseSquare E
  have h₁ := kernel_centered_coordinate_identity S k
    (sparseAdditiveKernel_multiplier_real E (17 / 20)) a b ha hb
  have h₂ := kernel_centered_coordinate_identity S k₂
    (sparseAdditiveKernel_square_multiplier_real E (17 / 20)) a b ha hb
  change k (a - b) = residueKernelScalar S k + localPairing (residueKernelSide T S k) B +
    localPairing A (residueKernelSide S T k) + localPairing A (residueKernelLower S T k B) at h₁
  change k (a - b) * k (a - b) = residueKernelScalar S k₂ + localPairing (residueKernelSide T S k₂) B +
    localPairing A (residueKernelSide S T k₂) + localPairing A (residueKernelLower S T k₂ B) at h₂
  change (1 + u * k (a - b)) * (1 + v * k (a - b)) =
    1 + (u + v) * residueKernelScalar S k + (u * v) * residueKernelScalar S k₂ +
    localPairing (fun x => conj (u + v) * residueKernelSide T S k x +
      conj (u * v) * residueKernelSide T S k₂ x) B +
    localPairing A (fun x => (u + v) * residueKernelSide S T k x +
      (u * v) * residueKernelSide S T k₂ x) +
    localPairing A (fun x => (u + v) * residueKernelLower S T k B x +
      (u * v) * residueKernelLower S T k₂ B x)
  rw [localPairing_left, localPairing_right, localPairing_right]
  simp only [starRingEnd_apply, star_star]
  linear_combination (u + v) * h₁ + (u * v) * h₂

end Ostmann

end OAI
