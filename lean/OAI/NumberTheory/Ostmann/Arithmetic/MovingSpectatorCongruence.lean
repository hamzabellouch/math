import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSpectator
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPeriodBound

namespace OAI

/-! # Residue constancy of the actual moving spectator recursion

The extra denominator clears the integer divisions along both children.
No coprimality between a spectator prime and a node frequency is required.
-/

namespace Ostmann
open scoped Classical

def movingSpectatorDenominator {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ
  | _, .leaf _ _ => 1
  | _, .node s _ _ U left right =>
      s * (MovingSlotReversal.naturalProduct value U : ℤ) *
        movingSpectatorDenominator value left * movingSpectatorDenominator value right

theorem movingSpectatorDenominator_ne_zero {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) : movingSpectatorDenominator value T ≠ 0 := by
  induction T with
  | leaf => exact one_ne_zero
  | node s CL CR U left right ihL ihR =>
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hf.1
      (Nat.cast_ne_zero.mpr (MovingSlotReversal.naturalProduct_ne_zero value hvalue U)))
      (ihL hf.2.1)) (ihR hf.2.2)

/-- Exact division by the node denominator loses that factor of the input
period. Both pivots are the original integer pivots. -/
theorem MovingSlotReversal.pivot_modEq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (s : MovingSlotReversal σ)
    (hs : s.rootFrequency ≠ 0) (XL XR YL YR : ℕ) (m : ℤ)
    (hX : s.IntegralAt value (XL, XR)) (hY : s.IntegralAt value (YL, YR))
    (hL : (XL : ℤ) ≡ (YL : ℤ) [ZMOD
      s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ) * m])
    (hR : (XR : ℤ) ≡ (YR : ℤ) [ZMOD
      s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ) * m]) :
    (s.naturalPivot value XL XR : ℤ) ≡ (s.naturalPivot value YL YR : ℤ) [ZMOD m] := by
  have h := ((hR.mul_right (naturalProduct value s.rightSlots)).mul_left s.leftFrequency).sub
    ((hL.mul_right (naturalProduct value s.leftSlots)).mul_left s.rightFrequency)
  have hx := hX.2
  have hy := hY.2
  simp only [Nat.cast_mul] at hx hy
  rw [hx, hy] at h
  simp only [← mul_assoc] at h
  exact Int.ModEq.mul_left_cancel'
    (mul_ne_zero hs (Nat.cast_ne_zero.mpr (naturalProduct_ne_zero value hvalue _))) h

/-- On integral histories, the full spectator function is constant on the
cleared top residue class, including its zero-at-nonunit convention. -/
theorem movingSlotSpectator_modEq {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR YL YR : ℕ)
    (hX : T.Integral value XL XR) (hY : T.Integral value YL YR)
    (hL : (XL : ℤ) ≡ (YL : ℤ) [ZMOD (q : ℤ) * movingSpectatorDenominator value T])
    (hR : (XR : ℤ) ≡ (YR : ℤ) [ZMOD (q : ℤ) * movingSpectatorDenominator value T]) :
    movingSlotSpectator value g D T XL XR = movingSlotSpectator value g D T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular =>
    simp only [movingSpectatorDenominator, mul_one] at hL hR
    have hl : (XL : ZMod q) = (YL : ZMod q) := by
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ q).mpr hL
    have hr : (XR : ZMod q) = (YR : ZMod q) := by
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ q).mpr hR
    simp only [movingSlotSpectator, Nat.cast_mul, hl, hr]
  | node s CL CR U left right ihL ihR =>
    let c : ℤ := s * (MovingSlotReversal.naturalProduct value U : ℤ)
    let dl := movingSpectatorDenominator value left
    let dr := movingSpectatorDenominator value right
    let step := MovingSlotData.step s CL CR U left right false
    let p := step.naturalPivot value XL XR
    let r := step.naturalPivot value YL YR
    have hL' : (XL : ℤ) ≡ (YL : ℤ) [ZMOD c * ((q : ℤ) * dl * dr)] := by
      convert hL using 1
      dsimp [c, dl, dr, movingSpectatorDenominator]
      ring
    have hR' : (XR : ℤ) ≡ (YR : ℤ) [ZMOD c * ((q : ℤ) * dl * dr)] := by
      convert hR using 1
      dsimp [c, dl, dr, movingSpectatorDenominator]
      ring
    have hp : (p : ℤ) ≡ (r : ℤ) [ZMOD (q : ℤ) * dl * dr] :=
      step.pivot_modEq value hvalue hf.1 XL XR YL YR _ hX.1 hY.1 hL' hR'
    have hpq : (p : ZMod q) = (r : ZMod q) := by
      have hp' := hp.of_dvd (show (q : ℤ) ∣ (q : ℤ) * dl * dr from
        ⟨dl * dr, by ring⟩)
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ q).mpr hp'
    have hpl : (p : ℤ) ≡ (r : ℤ) [ZMOD (q : ℤ) * dl] :=
      hp.of_dvd ⟨dr, rfl⟩
    have hpr : (p : ℤ) ≡ (r : ℤ) [ZMOD (q : ℤ) * dr] :=
      hp.of_dvd ⟨dl, by ring⟩
    have hll : (XL : ℤ) ≡ (YL : ℤ) [ZMOD (q : ℤ) * dl] :=
      hL'.of_dvd ⟨c * dr, by ring⟩
    have hrr : (XR : ℤ) ≡ (YR : ℤ) [ZMOD (q : ℤ) * dr] :=
      hR'.of_dvd ⟨c * dl, by ring⟩
    have hl := ihL hf.2.1 p XL r YL hX.2.1 hY.2.1 hpl hll
    have hr := ihR hf.2.2 p XR r YR hX.2.2 hY.2.2 hpr hrr
    change (if (p : ZMod q) = 0 then 0 else
      movingSlotSpectator value g D left p XL * star (movingSlotSpectator value g D right p XR)) =
      (if (r : ZMod q) = 0 then 0 else
      movingSlotSpectator value g D left r YL * star (movingSlotSpectator value g D right r YR))
    rw [hpq, hl, hr]

/-- The extra modulus has only one frequency and one compensation product
per internal node. Bulk-list lengths do not enter it. -/
theorem movingSpectatorDenominator_bound {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (B : ℕ)
    (hf : T.Frequencies (fun s => s.natAbs ≤ B))
    (hU : T.CompensationBound value B) :
    (movingSpectatorDenominator value T).natAbs ≤ B ^ (2 * (2 ^ n - 1)) := by
  induction T with
  | leaf => simp [movingSpectatorDenominator]
  | @node n s CL CR U left right ihL ihR =>
    have he : 2 + (2 * (2 ^ n - 1) + 2 * (2 ^ n - 1)) = 2 * (2 ^ (n + 1) - 1) := by
      have hp : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ]
      omega
    simp only [movingSpectatorDenominator, Int.natAbs_mul, Int.natAbs_natCast]
    calc
      _ ≤ B * B * B ^ (2 * (2 ^ n - 1)) * B ^ (2 * (2 ^ n - 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hf.1 hU.1)
          (ihL hf.2.1 hU.2.1)) (ihR hf.2.2 hU.2.2)
      _ = B ^ (2 + (2 * (2 ^ n - 1) + 2 * (2 ^ n - 1))) := by
        simp only [pow_add, pow_two]
        ring
      _ = _ := congrArg (B ^ ·) he

theorem movingSlotSpectator_norm {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ z, ‖g z‖ ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    ‖movingSlotSpectator value g D T XL XR‖ ≤ B ^ (2 ^ n) := by
  induction T generalizing XL XR with
  | leaf s regular => simpa only [movingSlotSpectator, pow_zero, pow_one] using hg _
  | @node n s CL CR U left right ihL ihR =>
    rw [movingSlotSpectator]
    split_ifs
    · simp only [norm_zero]
      exact pow_nonneg hB _
    · rw [norm_mul, norm_star]
      calc
        _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
          mul_le_mul (ihL _ _) (ihR _ _) (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
