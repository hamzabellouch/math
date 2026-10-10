import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantArchimedean

namespace OAI

/-! # Polynomial smooth factors in the full moving-giant coefficient -/

namespace Ostmann
open scoped Classical ComplexConjugate

noncomputable def movingFourierLeaf {σ : Type*} (value : σ → ℕ)
    (ψ : ℝ → ℂ) (X : ℝ) (x : MovingSlotState σ) (s : ℤ) : ℂ :=
  normalizedFourierProfile ψ s ((movingSlotModulus value x : ℝ) / X)

noncomputable def movingFourierTree {σ : Type*} (value : σ → ℕ) (ψ : ℝ → ℂ) (X : ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → ℂ
  | _, .leaf s regular, XL, XR =>
      normalizedFourierProfile ψ s
        ((XL * XR * MovingSlotReversal.naturalProduct value regular : ℕ) / X)
  | _, .node s CL CR u left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
      movingFourierTree value ψ X left p XL * star (movingFourierTree value ψ X right p XR)

noncomputable def movingPolynomialFourierTree {σ : Type*}
    (value : σ → ℕ) (ψ : ℝ → ℂ) (X z : ℝ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ → ℂ
  | _, .leaf s regular, L, R =>
      normalizedFourierProfile ψ s
        ((L * R * Polynomial.C (MovingSlotReversal.naturalProduct value regular : ℝ)).eval z / X)
  | _, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).pivotPolynomial value L R
      movingPolynomialFourierTree value ψ X z left p L *
        star (movingPolynomialFourierTree value ψ X z right p R)

theorem movingPolynomialFourierTree_eq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (ψ : ℝ → ℂ) (X z : ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (hfreq : T.Frequencies (· ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) (L R : Polynomial ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    movingPolynomialFourierTree value ψ X z T L R = movingFourierTree value ψ X T XL XR := by
  induction T generalizing XL XR L R with
  | leaf s regular =>
    simp only [movingPolynomialFourierTree, movingFourierTree, Polynomial.eval_mul,
      Polynomial.eval_C, hL, hR, Nat.cast_mul]
  | node s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    have hp : (step.pivotPolynomial value L R).eval z = (step.naturalPivot value XL XR : ℝ) := by
      rw [MovingSlotReversal.pivotPolynomial_eval, hL, hR]
      exact step.realPivot_eq value XL XR hfreq.1
        (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) hI.1
    exact congrArg₂ (fun a b : ℂ => a * star b)
      (ihL hfreq.2.1 _ _ hI.2.1 _ _ hp hL) (ihR hfreq.2.2 _ _ hI.2.2 _ _ hp hR)

/-- The exact Fourier factorization preserves all original support terms,
including terms whose full coefficient is zero. -/
theorem movingSlotWeight_fourier {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (ψ : ℝ → ℂ) (X : ℝ) {n : ℕ}
    (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => F x s * movingFourierLeaf value ψ X x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t *
        movingFourierTree value ψ X T XL XR := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular =>
    have hs : s = t := hT
    simp only [recursiveTransferWeight, movingFourierLeaf, movingSlotModulus,
      movingFourierTree, hs]
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
    have hp : historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
        MovingSlotReversal.naturalProduct value u = p := by
      simp only [historyPivot, sys, movingSlotSystem,
        MovingSlotState.leftProduct, MovingSlotState.rightProduct, x,
        ← hT.1, ← hT.2.1.root, ← hT.2.2.root, p,
        MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one]
    change recursiveTransferWeight sys _ cutoff (n + 1) x t = _
    simp only [recursiveTransferWeight]
    split_ifs
    · change (cutoff x t.1 _ _ : ℂ) *
          recursiveTransferWeight sys _ cutoff n ⟨n, left, _, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys _ cutoff n ⟨n, right, _, XR⟩ t.2.2) =
        ((cutoff x t.1 _ _ : ℂ) * recursiveTransferWeight sys F cutoff n ⟨n, left, _, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys F cutoff n ⟨n, right, _, XR⟩ t.2.2)) * _
      rw [hp, ihL t.2.1 hT.2.1 p XL, ihR t.2.2 hT.2.2 p XR]
      change _ = _ * (movingFourierTree value ψ X left p XL * star (movingFourierTree value ψ X right p XR))
      simp only [star_mul]
      ring
    · exact (zero_mul _).symm

/-- The polynomial smooth extension agrees with the full coefficient on
its proved integer support. No polynomial realization premise is required. -/
theorem movingSlotWeight_polynomial_fourier {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (ψ : ℝ → ℂ) (X z : ℝ) {n : ℕ}
    (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : Polynomial ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => F x s * movingFourierLeaf value ψ X x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t *
        movingPolynomialFourierTree value ψ X z T L R := by
  rw [movingSlotWeight_fourier value childBound pivotBound F extra ψ X T t hT XL XR]
  by_cases hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t = 0
  · rw [hw, zero_mul, zero_mul]
  · have hi := movingSlotWeight_nonzero_integral value childBound pivotBound F extra T t hT XL XR hw
    rw [movingPolynomialFourierTree_eq value hvalue ψ X z T hfreq XL XR hi L R hL hR]

end Ostmann

end OAI
