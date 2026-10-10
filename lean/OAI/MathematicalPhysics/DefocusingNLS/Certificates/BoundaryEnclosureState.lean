import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryEnclosureInputs

namespace OAI

/-! # Soundness of the complete uncertain forward recurrence -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate
open GaussianEnclosure

abbrev PolynomialState := ((Polynomial ℂ × Polynomial ℂ) × (Polynomial ℂ × Polynomial ℂ))

noncomputable def polynomialStep (M s t : Polynomial ℂ) (xy : PolynomialState) : PolynomialState :=
  let x₀ := t * xy.1.1 + s * xy.2.1
  let x₁ := t * xy.1.2 + s * xy.2.2
  ((x₀, x₁), ((t - M) * xy.2.1 - x₀, (t - M) * xy.2.2 - x₁))

noncomputable def polynomialState (ell : ℕ) (b Z : ℝ) : ℕ → PolynomialState
  | 0 => ((1, 0), (0, 1))
  | n + 1 => polynomialStep (C ((100000000 * (ell + 5) : ℤ) : ℂ))
      (inputS Z) (inputT ell n b) (polynomialState ell b Z n)

def EnclosesState (xy : State) (pq : PolynomialState) : Prop :=
  EnclosesPolynomial xy.1.1 pq.1.1 ∧ EnclosesPolynomial xy.1.2 pq.1.2 ∧
    EnclosesPolynomial xy.2.1 pq.2.1 ∧ EnclosesPolynomial xy.2.2 pq.2.2

theorem step_sound (ell n : ℕ) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    {xy : State} {pq : PolynomialState} (h : EnclosesState xy pq) :
    EnclosesState (step ell n xy)
      (polynomialStep (C ((100000000 * (ell + 5) : ℤ) : ℂ)) (inputS Z) (inputT ell n b) pq) := by
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := h
  have ht := inputT_sound ell n b hb
  have hs := inputS_sound Z hZ
  have hM := constant_sound (100000000 * (ell + 5))
  have hd := subPolynomial_sound ht hM
  have hx₀' := addPolynomial_sound (mulPolynomial_sound ht hx₀) (mulPolynomial_sound hs hy₀)
  have hx₁' := addPolynomial_sound (mulPolynomial_sound ht hx₁) (mulPolynomial_sound hs hy₁)
  exact ⟨hx₀', hx₁', subPolynomial_sound (mulPolynomial_sound hd hy₀) hx₀',
    subPolynomial_sound (mulPolynomial_sound hd hy₁) hx₁'⟩

/-- Every coefficient enclosure is valid for the same actual parameter pair. -/
theorem state_sound (ell : ℕ) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (n : ℕ) : EnclosesState (state ell n) (polynomialState ell b Z n) := by
  induction n with
  | zero =>
    exact ⟨by simpa [state, polynomialState] using constant_sound 1,
      by simpa [state, polynomialState] using constant_sound 0,
      by simpa [state, polynomialState] using constant_sound 0,
      by simpa [state, polynomialState] using constant_sound 1⟩
  | succ n ih => exact step_sound ell n b Z hb hZ ih

attribute [local irreducible] state polynomialState

/-- The raw determinant enclosure bounds the coherent determinant before any
reality, parity or degree truncation is applied. -/
theorem determinant_sound (ell : ℕ) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2) :
    let pq := polynomialState ell b Z 8
    let M := ((100000000 * (ell + 5) : ℤ) : ℂ)
    let s := Complex.I * (100000000 * Z : ℝ)
    let A := C M * conjugatePolynomial pq.1.1 * pq.1.1 +
      C s * (conjugatePolynomial pq.1.1 * pq.2.1 - conjugatePolynomial pq.2.1 * pq.1.1)
    let D := C M * conjugatePolynomial pq.1.2 * pq.1.2 +
      C s * (conjugatePolynomial pq.1.2 * pq.2.2 - conjugatePolynomial pq.2.2 * pq.1.2)
    let C' := C M * conjugatePolynomial pq.1.1 * pq.1.2 +
      C s * (conjugatePolynomial pq.1.1 * pq.2.2 - conjugatePolynomial pq.2.1 * pq.1.2)
    EnclosesPolynomial (determinant ell)
      ((A + sharpPolynomial A) * (D + sharpPolynomial D) -
        (C' + sharpPolynomial C') * conjugatePolynomial (C' + sharpPolynomial C')) := by
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := state_sound ell b Z hb hZ 8
  have hs := inputS_sound Z hZ
  have hA := symmetrize_sound (hermitian_sound ell _ hs hx₀ hy₀ hx₀ hy₀)
  have hD := symmetrize_sound (hermitian_sound ell _ hs hx₁ hy₁ hx₁ hy₁)
  have hC := symmetrize_sound (hermitian_sound ell _ hs hx₀ hy₀ hx₁ hy₁)
  exact subPolynomial_sound (mulPolynomial_sound hA hD)
    (mulPolynomial_sound hC (conjPolynomial_sound hC))

end DefocusingNLS.BoundaryCertificate

end OAI
