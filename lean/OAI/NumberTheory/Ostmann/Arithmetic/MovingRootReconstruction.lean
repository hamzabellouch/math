import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalSampleExpansion
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeArithmeticTransfer

namespace OAI

/-! # The integer substitution is the giant in the original node coefficient -/

namespace Ostmann
open scoped Classical

/-- The composite pivot reconstructed by the history system is the
compensation product times the reconstructed giant. -/
theorem reconstructedPivot_compensation (I : Finset ℕ) (N s : ℤ) (U : ℕ)
    (h : validTransferredPivot I N (s * U)) :
    reconstructedPivot N s = reconstructedPivot N (s * U) * U := by
  have hs : s ≠ 0 := left_ne_zero_of_mul h.1
  have he := validTransferredPivot_equation I N (s * U) h
  apply reconstructedPivot_of_eq N s hs
  push_cast
  calc
    N = (s * U) * reconstructedPivot N (s * U) := he
    _ = _ := by ring

theorem reconstructedGiant_eq_div (I : Finset ℕ) (N s : ℤ) (U : ℕ)
    (hU : 0 < U) (h : validTransferredPivot I N (s * U)) :
    reconstructedPivot N s / U = reconstructedPivot N (s * U) := by
  rw [reconstructedPivot_compensation I N s U h, Nat.mul_div_left _ hU]

/-- Conversely the original composite-pivot integrality test gives exactly
one positive giant in the retained integer range. -/
theorem validTransferredGiant_of_composite (I : Finset ℕ)
    (N s : ℤ) (P U : ℕ) (hs : s ≠ 0) (hP : 0 < P) (hU : 0 < U)
    (hdiv : U ∣ P) (hI : P / U ∈ I) (hrel : N = s * P) :
    validTransferredPivot I N (s * U) := by
  have he : P / U * U = P := Nat.div_mul_cancel hdiv
  have hp : 0 < P / U := by
    by_contra hn
    have hz : P / U = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, zero_mul] at he
    omega
  apply validTransferredPivot_of_eq I N (s * U)
    (mul_ne_zero hs (by exact_mod_cast hU.ne')) (P / U) hp hI
  calc
    N = s * (P : ℤ) := hrel
    _ = s * (((P / U) * U : ℕ) : ℤ) := by rw [he]
    _ = (s * (U : ℤ)) * ((P / U : ℕ) : ℤ) := by rw [Nat.cast_mul]; ring

/-- The node's original factor is exactly `U φ(log p - G)`, where `p` is
reconstructed from the same signed quotient as the integer off-diagonal. -/
theorem movingOriginalNode_reconstructed {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (x : MovingSlotState σ) (s v w : ℤ)
    (hU : 0 < x.compensation value)
    (h : validTransferredPivot I
      (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ))
      (s * x.compensation value)) :
    movingSlotCutoff value childBound pivotBound
      (movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G))
        x s v w =
      (x.compensation value : ℝ) * φ
        (Real.log (reconstructedPivot
          (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ))
          (s * x.compensation value)) - G x.depth) := by
  let N := v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)
  let U := x.compensation value
  let p := reconstructedPivot N (s * U)
  have hP : historyPivot (movingSlotSystem value childBound pivotBound) x s v w = p * U :=
    reconstructedPivot_compensation I N s U h
  have hdiv : U ∣ historyPivot (movingSlotSystem value childBound pivotBound) x s v w := by
    rw [hP]
    exact dvd_mul_left U p
  have hquot : historyPivot (movingSlotSystem value childBound pivotBound) x s v w / U = p := by
    rw [hP, Nat.mul_div_left _ hU]
  have hp : 0 < (p : ℝ) := by exact_mod_cast hI p h.2.2.2
  unfold movingSlotCutoff
  rw [ite_eq_left ⟨hU, hdiv⟩]
  change (U : ℝ) * (1 * positiveLogCutoff φ (G x.depth)
    (historyPivot (movingSlotSystem value childBound pivotBound) x s v w / U : ℕ)) = _
  rw [hquot, one_mul, positiveLogCutoff, ite_eq_left hp]

/-- An unconditional node formula in terms of the reconstructed giant.
All original frequency, range, and coprimality tests remain in the guard. -/
theorem movingSampleRootFactor_reconstructed {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (t : FrequencyTree ℤ (n + 1)) (CL CR u : List σ) (XL XR : ℕ) :
    let x := movingRootState n t CL CR u XL XR
    let sys := movingSlotSystem value childBound pivotBound
    let v := frequencyRoot n t.2.1
    let w := frequencyRoot n t.2.2
    let U := x.compensation value
    let p := reconstructedPivot (v * (x.rightProduct value : ℤ) -
      w * (x.leftProduct value : ℤ)) (t.1 * U)
    movingSampleRootFactor value childBound pivotBound
      (movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G))
        n t CL CR u XL XR =
      if ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U then
        ((U : ℝ) * φ (Real.log p - G (n + 1)) : ℂ) else 0 := by
  dsimp only
  let x := movingRootState n t CL CR u XL XR
  let sys := movingSlotSystem value childBound pivotBound
  let v := frequencyRoot n t.2.1
  let w := frequencyRoot n t.2.2
  let U := x.compensation value
  let N := v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)
  let p := reconstructedPivot N (t.1 * U)
  let P := historyPivot sys x t.1 v w
  change (if ValidTransferNode sys x t.1 v w P then
    (movingSlotCutoff value childBound pivotBound
      (movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G))
      x t.1 v w : ℂ) else 0) =
    if ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U then
      ((U : ℝ) * φ (Real.log p - G (n + 1)) : ℂ) else 0
  by_cases h : ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U
  · have hP : P = p * U := h.1.historyPivot_eq
    have hp : 0 < p := Nat.pos_of_mul_pos_right h.1.pivot_pos
    have he : N = (t.1 * (U : ℤ)) * p := by
      have hh := h.1.relation
      change N = t.1 * ((p * U : ℕ) : ℤ) at hh
      rw [Nat.cast_mul] at hh
      calc
        N = t.1 * ((p : ℤ) * U) := hh
        _ = _ := by ring
    have hvalid : validTransferredPivot {p} N (t.1 * U) :=
      validTransferredPivot_of_eq {p} N (t.1 * U)
        (mul_ne_zero h.1.root_ne_zero (by exact_mod_cast h.2.ne')) p hp (by simp) he
    have hcut := movingOriginalNode_reconstructed value childBound pivotBound φ G
      {p} (fun q hq => by simpa only [Finset.mem_singleton.mp hq] using hp)
      x t.1 v w h.2 hvalid
    rw [ite_eq_left h, hP, ite_eq_left h.1, hcut]
    simp only [Complex.ofReal_mul]
    rfl

  · rw [ite_eq_right h]
    by_cases hv : ValidTransferNode sys x t.1 v w P
    · rw [ite_eq_left hv]
      have hdiv : ¬(0 < U ∧ U ∣ P) := by
        rintro ⟨hU, hd⟩
        have hh := validTransferredGiant_of_composite {P / U} N t.1 P U
          hv.root_ne_zero hv.pivot_pos hU hd (by simp) hv.relation
        have he : P / U = p := (reconstructedGiant_eq_div {P / U} N t.1 U hU hh)
        have hPU : P = p * U := by rw [← he]; exact (Nat.div_mul_cancel hd).symm
        exact h ⟨hPU ▸ hv, hU⟩
      change ((if 0 < U ∧ U ∣ P then _ else 0 : ℝ) : ℂ) = 0
      rw [ite_eq_right hdiv, Complex.ofReal_zero]
    · rw [ite_eq_right hv]

/-- The full current-state support guard commutes with root extraction.
Its subtree-frequency unit tests are not discarded by the integer change
of variables. -/
theorem movingSampleRootFactor_guarded {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (n : ℕ)
    (t : FrequencyTree ℤ (n + 1)) (CL CR u : List σ) (XL XR : ℕ) :
    movingSampleRootFactor value childBound pivotBound (movingGuardedExtra value outside E)
      n t CL CR u XL XR =
      if movingLocalSupport value outside (movingRootState n t CL CR u XL XR) then
        movingSampleRootFactor value childBound pivotBound E n t CL CR u XL XR else 0 := by
  unfold movingSampleRootFactor
  dsimp only
  rw [movingSlotCutoff_guarded]
  split_ifs <;> rfl

end Ostmann

end OAI
