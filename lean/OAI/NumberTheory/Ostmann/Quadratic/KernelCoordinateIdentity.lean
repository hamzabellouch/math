import OAI.NumberTheory.Ostmann.Characters.FiniteKernelCoordinates

namespace OAI

/-! # Exact identification of the centered-coordinate kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem rawKernel_pairing_add {p : ℕ} [NeZero p]
    (k f₁ f₂ g₁ g₂ : ZMod p → ℂ) :
    (∑ x, conj (f₁ x + f₂ x) * rawAdditiveKernelAction k (fun x => g₁ x + g₂ x) x) =
      (∑ x, conj (f₁ x) * rawAdditiveKernelAction k g₁ x) +
      (∑ x, conj (f₁ x) * rawAdditiveKernelAction k g₂ x) +
      (∑ x, conj (f₂ x) * rawAdditiveKernelAction k g₁ x) +
      (∑ x, conj (f₂ x) * rawAdditiveKernelAction k g₂ x) := by
  rw [rawAdditiveKernelAction_add_input]
  simp only [map_add, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem centeredSupportProjection_pairing_range {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (f g : ZMod p → ℂ) :
    (∑ x, conj (centeredSupportProjection S f x) * centeredSupportProjection S g x) =
      ∑ x, conj (centeredSupportProjection S f x) * g x := by
  rw [centeredSupportProjection_pairing, centeredSupportProjection_idempotent]

/-- The four blocks really represent `k(a-b)` on the centered coordinates of
the two residue points. This is the identity used before tensoring. -/
theorem kernel_centered_coordinate_identity {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (k : ZMod p → ℂ)
    (hk : ∀ c, conj ((p : ℂ) * additiveFourier k c) = (p : ℂ) * additiveFourier k c)
    (a b : ZMod p) (ha : a ∈ S) (hb : b ∈ Finset.univ \ S) :
    k (a - b) = residueKernelScalar S k +
      (∑ x, conj (residueKernelSide (Finset.univ \ S) S k x) *
        centeredSupportProjection (Finset.univ \ S) (residuePointVector b) x) +
      (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
        residueKernelSide S (Finset.univ \ S) k x) +
      (∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
        residueKernelLower S (Finset.univ \ S) k
          (centeredSupportProjection (Finset.univ \ S) (residuePointVector b)) x) := by
  let T := Finset.univ \ S
  let A := centeredSupportProjection S (residuePointVector a)
  let B := centeredSupportProjection T (residuePointVector b)
  have harg := congrArg₂ (fun f g : ZMod p → ℂ =>
    ∑ x, conj (f x) * rawAdditiveKernelAction k g x)
    (residuePointVector_decomposition S a ha)
    (residuePointVector_decomposition T b hb)
  have hexpand := rawKernel_pairing_add k (uniformResidueVector S) A (uniformResidueVector T) B
  rw [residuePointVector_kernel] at harg
  have hrow := residueKernel_row_pairing S T k hk B
  have hB : centeredSupportProjection T B = B := centeredSupportProjection_idempotent T _
  rw [hB] at hrow
  have hcol := centeredSupportProjection_pairing_range S (residuePointVector a)
    (rawAdditiveKernelAction k (uniformResidueVector T))
  have hlower := centeredSupportProjection_pairing_range S (residuePointVector a)
    (rawAdditiveKernelAction k B)
  have hlow : residueKernelLower S T k B = centeredSupportProjection S (rawAdditiveKernelAction k B) := by
    unfold residueKernelLower
    rw [hB]
  change k (a - b) = _
  change k (a - b) =
    (∑ x, conj (uniformResidueVector S x) * rawAdditiveKernelAction k (uniformResidueVector T) x) +
      (∑ x, conj (residueKernelSide T S k x) * B x) +
      (∑ x, conj (A x) * centeredSupportProjection S (rawAdditiveKernelAction k (uniformResidueVector T)) x) +
      (∑ x, conj (A x) * residueKernelLower S T k B x)
  rw [hlow, hcol, hlower, ← hrow]
  exact harg.trans hexpand

end Ostmann

end OAI
