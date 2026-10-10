import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierVariation

namespace OAI

/-! # The supported original coefficient is the constructed polynomial weight -/

namespace Ostmann
open scoped Classical SchwartzMap

/-- Every terminal factor of a nonzero recursive coefficient is nonzero.
This statement keeps the concrete moving giant and terminal modulus. -/
theorem movingSlotWeight_leaf_support {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (P : ℕ → ℤ → Prop)
    (hF : ∀ x s, F x s ≠ 0 → P (movingSlotModulus value x) s)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t ≠ 0) :
    ∀ i, P (T.leafModuli value XL XR i) (T.leafFrequencies i) := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular =>
    intro i
    have hs : s = t := hT
    subst s
    exact hF ⟨0, .leaf t regular, XL, XR⟩ t hw
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
    have hp : historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
        MovingSlotReversal.naturalProduct value u = p := by
      simp only [historyPivot, sys, movingSlotSystem, MovingSlotState.leftProduct,
        MovingSlotState.rightProduct, x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root, p,
        MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one]
    have hvalid := recursiveTransferWeight_nonzero_valid sys F cutoff (n + 1) x t hw
    obtain ⟨Q, hQ, _, _⟩ := hvalid
    have hnode := recursiveTransferWeight_node sys F cutoff n x t Q hQ
    have hQp : Q / MovingSlotReversal.naturalProduct value u = p := by
      rw [← hQ.historyPivot_eq]
      exact hp
    have hL : recursiveTransferWeight sys F cutoff n ⟨n, left, p, XL⟩ t.2.1 ≠ 0 := by
      intro hz
      apply hw
      rw [hnode]
      change (cutoff x t.1 _ _ : ℂ) *
        recursiveTransferWeight sys F cutoff n ⟨n, left, Q / _, XL⟩ t.2.1 * _ = 0
      rw [hQp, hz, mul_zero, zero_mul]
    have hR : recursiveTransferWeight sys F cutoff n ⟨n, right, p, XR⟩ t.2.2 ≠ 0 := by
      intro hz
      apply hw
      rw [hnode]
      change _ * star (recursiveTransferWeight sys F cutoff n ⟨n, right, Q / _, XR⟩ t.2.2) = 0
      rw [hQp, hz, star_zero, mul_zero]
    intro i
    cases i with
    | inl i => exact ihL t.2.1 hT.2.1 p XL hL i
    | inr i => exact ihR t.2.2 hT.2.2 p XR hR i

noncomputable def movingWindowLeaf {σ : Type*} (value : σ → ℕ)
    (X lo hi : ℝ) (F : MovingSlotState σ → ℤ → ℂ) (x : MovingSlotState σ) (s : ℤ) : ℂ :=
  if (movingSlotModulus value x : ℝ) / X ∈ Set.Icc lo hi then F x s else 0

/-- The original sharp terminal windows suffice for the clipped polynomial
extension. All node and prime restrictions remain in the scalar coefficient. -/
theorem moving_windowed_fourier_polynomial {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hfreq : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : Polynomial ℝ) (z : ℝ)
    (hL : L.eval z = (XL : ℝ)) (hR : R.eval z = (XR : ℝ)) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => movingWindowLeaf value X lo hi F x s * movingFourierLeaf value ψ X x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
        n ⟨n, T, XL, XR⟩ t *
        smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z := by
  rw [movingSlotWeight_polynomial_fourier value hvalue childBound pivotBound
    (movingWindowLeaf value X lo hi F) extra ψ X z T t hT hfreq XL XR L R hL hR]
  by_cases hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingWindowLeaf value X lo hi F) (movingSlotCutoff value childBound pivotBound extra)
      n ⟨n, T, XL, XR⟩ t = 0
  · rw [hw, zero_mul, zero_mul]
  · have hI := movingSlotWeight_nonzero_integral value childBound pivotBound
      (movingWindowLeaf value X lo hi F) extra T t hT XL XR hw
    have hr := movingSlotWeight_leaf_support value childBound pivotBound
      (movingWindowLeaf value X lo hi F) extra (fun M _ => (M : ℝ) / X ∈ Set.Icc lo hi)
      (fun x s hx => by
        by_contra hn
        exact hx (by simp only [movingWindowLeaf, ite_eq_right hn])) T t hT XL XR hw
    rw [movingFourierPolynomialFactors_value value T L R ψ X lo hi hlo hhi z]
    intro i
    rw [T.leafPolynomials_eval value hvalue hfreq XL XR hI L R z hL hR i]
    exact hr i

end Ostmann

end OAI
