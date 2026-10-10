import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSpectator
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceUnits
import OAI.NumberTheory.Ostmann.Characters.NormalizedFourierProfile
import OAI.NumberTheory.Ostmann.Characters.TreeTupleProfiles

namespace OAI

/-! # The actual terminal moduli as quadratic functions of a top giant

Small prime values are fixed here. Every reconstructed giant is linear in the
initial pair, and each terminal modulus is a product of two such linear forms.
The identification uses the integer support equations of the original sampler.
-/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.realPivot {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : ℝ) : ℝ :=
  ((s.leftFrequency : ℝ) * (MovingSlotReversal.naturalProduct value s.rightSlots : ℝ) * XR -
    (s.rightFrequency : ℝ) * (MovingSlotReversal.naturalProduct value s.leftSlots : ℝ) * XL) /
    ((s.rootFrequency : ℝ) * (MovingSlotReversal.naturalProduct value s.compensationSlots : ℝ))

theorem MovingSlotReversal.realPivot_eq {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : ℕ)
    (hs : s.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value s.compensationSlots ≠ 0)
    (h : s.IntegralAt value (XL, XR)) :
    s.realPivot value XL XR = (s.naturalPivot value XL XR : ℝ) := by
  have he := congrArg (fun z : ℤ => (z : ℝ)) h.2
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
  unfold realPivot
  apply (div_eq_iff (mul_ne_zero (Int.cast_ne_zero.mpr hs) (Nat.cast_ne_zero.mpr hu))).mpr
  nlinarith only [he]

noncomputable def MovingSlotReversal.pivotPolynomial {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (((s.rootFrequency : ℝ) *
      (MovingSlotReversal.naturalProduct value s.compensationSlots : ℝ))⁻¹) *
    (Polynomial.C ((s.leftFrequency : ℝ) *
        (MovingSlotReversal.naturalProduct value s.rightSlots : ℝ)) * XR -
      Polynomial.C ((s.rightFrequency : ℝ) *
        (MovingSlotReversal.naturalProduct value s.leftSlots : ℝ)) * XL)

theorem MovingSlotReversal.pivotPolynomial_eval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : Polynomial ℝ) (z : ℝ) :
    (s.pivotPolynomial value XL XR).eval z = s.realPivot value (XL.eval z) (XR.eval z) := by
  simp only [pivotPolynomial, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    realPivot, div_eq_mul_inv]
  ring

theorem MovingSlotReversal.pivotPolynomial_degree {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : Polynomial ℝ) (d : ℕ)
    (hL : XL.natDegree ≤ d) (hR : XR.natDegree ≤ d) :
    (s.pivotPolynomial value XL XR).natDegree ≤ d := by
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, zero_add] using hR)
  · exact Polynomial.natDegree_mul_le.trans (by simpa only [Polynomial.natDegree_C, zero_add] using hL)

/-- The terminal integer moduli, with the same pivot divisions and child order
as the full recursive coefficient. -/
def MovingSlotData.leafModuli {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → TreeLeafIndex n → ℕ
  | _, .leaf _ regular, XL, XR, _ => XL * XR * MovingSlotReversal.naturalProduct value regular
  | _, .node s CL CR u left right, XL, XR, i =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
      match i with
      | .inl i => left.leafModuli value p XL i
      | .inr i => right.leafModuli value p XR i

/-- Polynomial extension in one free top coordinate. Its coefficients may
contain reciprocals of the fixed frequency and compensation products. -/
noncomputable def MovingSlotData.leafPolynomials {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ →
      TreeLeafIndex n → Polynomial ℝ
  | _, .leaf _ regular, XL, XR, _ =>
      XL * XR * Polynomial.C (MovingSlotReversal.naturalProduct value regular : ℝ)
  | _, .node s CL CR u left right, XL, XR, i =>
      let p := (MovingSlotData.step s CL CR u left right false).pivotPolynomial value XL XR
      match i with
      | .inl i => left.leafPolynomials value p XL i
      | .inr i => right.leafPolynomials value p XR i

theorem MovingSlotData.leafPolynomials_degree {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : Polynomial ℝ) (d : ℕ)
    (hL : XL.natDegree ≤ d) (hR : XR.natDegree ≤ d) (i : TreeLeafIndex n) :
    (T.leafPolynomials value XL XR i).natDegree ≤ 2 * d := by
  induction T generalizing XL XR with
  | leaf s regular =>
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, add_zero]
    exact Polynomial.natDegree_mul_le.trans (by omega)
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).pivotPolynomial_degree
      value XL XR d hL hR
    cases i with
    | inl i => exact ihL _ _ hp hL i
    | inr i => exact ihR _ _ hp hR i

theorem MovingSlotReversal.naturalProduct_ne_zero {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (slots : List σ) :
    naturalProduct value slots ≠ 0 := by
  induction slots with
  | nil => simp [naturalProduct]
  | cons i slots ih =>
    simpa only [naturalProduct, List.map_cons, List.prod_cons] using mul_ne_zero (hvalue i) ih

/-- Exact agreement on integer support; no approximation or extra
real-variable realization condition is assumed. -/
theorem MovingSlotData.leafPolynomials_eval {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) {n : ℕ} (T : MovingSlotData σ n)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (hI : T.Integral value XL XR)
    (L R : Polynomial ℝ) (z : ℝ) (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ))
    (i : TreeLeafIndex n) :
    (T.leafPolynomials value L R i).eval z = (T.leafModuli value XL XR i : ℝ) := by
  induction T generalizing XL XR L R with
  | leaf s regular =>
    simp only [leafPolynomials, leafModuli, Polynomial.eval_mul, Polynomial.eval_C,
      hL, hR, Nat.cast_mul]
  | node s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    have hp : (step.pivotPolynomial value L R).eval z = (step.naturalPivot value XL XR : ℝ) := by
      rw [MovingSlotReversal.pivotPolynomial_eval, hL, hR]
      exact step.realPivot_eq value XL XR hfreq.1
        (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) hI.1
    cases i with
    | inl i => exact ihL hfreq.2.1 _ _ hI.2.1 _ _ hp hL i
    | inr i => exact ihR hfreq.2.2 _ _ hI.2.2 _ _ hp hR i

/-- In particular each leaf is quadratic in either initial giant. -/
theorem MovingSlotData.leftGiant_quadratic {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XR : ℝ) (i : TreeLeafIndex n) :
    (T.leafPolynomials value Polynomial.X (Polynomial.C XR) i).natDegree ≤ 2 := by
  simpa only [mul_one] using T.leafPolynomials_degree value Polynomial.X (Polynomial.C XR) 1
    (by simp) (by simp) i

end Ostmann

end OAI
