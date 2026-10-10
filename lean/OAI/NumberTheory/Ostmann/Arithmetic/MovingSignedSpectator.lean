import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCongruence

namespace OAI

/-! # Signed residue representatives for the literal spectator recursion -/

namespace Ostmann
open scoped Classical

/-- Clearing the input period makes division compatible with congruence,
even when the individual numerators are not divisible by the denominator. -/
theorem int_modEq_ediv (c m x y : ℤ) (hc : c ≠ 0)
    (h : x ≡ y [ZMOD c * m]) : x / c ≡ y / c [ZMOD m] := by
  have hr : x % c = y % c := h.of_mul_right m
  have hrem : x % c ≡ y % c [ZMOD c * m] := by rw [hr]
  have hx : x - x % c = c * (x / c) := by
    linear_combination -(Int.emod_add_mul_ediv x c)
  have hy : y - y % c = c * (y / c) := by
    linear_combination -(Int.emod_add_mul_ediv y c)
  have hh := h.sub hrem
  rw [hx, hy] at hh
  exact Int.ModEq.mul_left_cancel' hc hh

noncomputable def MovingSlotReversal.signedPivot {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (XL XR : ℤ) : ℤ :=
  (s.leftFrequency * (XR * (naturalProduct value s.rightSlots : ℤ)) -
    s.rightFrequency * (XL * (naturalProduct value s.leftSlots : ℤ))) /
      (s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ))

theorem MovingSlotReversal.signedPivot_nat {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (hs : s.rootFrequency ≠ 0)
    (XL XR : ℕ) (hI : s.IntegralAt value (XL, XR)) :
    s.signedPivot value XL XR = (s.naturalPivot value XL XR : ℤ) := by
  have he := hI.2
  simp only [Nat.cast_mul] at he
  unfold signedPivot
  rw [he, ← mul_assoc]
  exact Int.mul_ediv_cancel_left _
    (mul_ne_zero hs (Nat.cast_ne_zero.mpr (naturalProduct_ne_zero value hvalue _)))

noncomputable def movingSignedSpectator {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℂ
  | _, .leaf s regular, XL, XR =>
      g ((s : ZMod q) / ((D : ZMod q) *
        ((XL * XR * (MovingSlotReversal.naturalProduct value regular : ℤ) : ℤ) : ZMod q)))
  | _, .node s CL CR U left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).signedPivot value XL XR
      if (p : ZMod q) = 0 then 0 else
        movingSignedSpectator value g D left p XL * star (movingSignedSpectator value g D right p XR)

/-- Signed representatives agree with the original natural recursion on
its proved integral support. No extra unit condition is imposed. -/
theorem movingSignedSpectator_nat {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ)
    (hI : T.Integral value XL XR) :
    movingSignedSpectator value g D T XL XR = movingSlotSpectator value g D T XL XR := by
  induction T generalizing XL XR with
  | leaf s regular =>
    simp only [movingSignedSpectator, movingSlotSpectator, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  | node s CL CR U left right ihL ihR =>
    rw [movingSignedSpectator, movingSlotSpectator,
      (MovingSlotData.step s CL CR U left right false).signedPivot_nat value hvalue hf.1 XL XR hI.1]
    simp only [Int.cast_natCast]
    split_ifs
    · rfl
    · rw [ihL hf.2.1 _ _ hI.2.1, ihR hf.2.2 _ _ hI.2.2]

theorem MovingSlotReversal.signedPivot_modEq {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (hs : s.rootFrequency ≠ 0)
    (XL XR YL YR m : ℤ)
    (hL : XL ≡ YL [ZMOD s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ) * m])
    (hR : XR ≡ YR [ZMOD s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ) * m]) :
    s.signedPivot value XL XR ≡ s.signedPivot value YL YR [ZMOD m] := by
  unfold signedPivot
  apply int_modEq_ediv _ m _ _
    (mul_ne_zero hs (Nat.cast_ne_zero.mpr (naturalProduct_ne_zero value hvalue _)))
  exact ((hR.mul_right (naturalProduct value s.rightSlots)).mul_left s.leftFrequency).sub
    ((hL.mul_right (naturalProduct value s.leftSlots)).mul_left s.rightFrequency)

/-- Signed representatives are periodic before imposing any real support. -/
theorem movingSignedSpectator_modEq {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR YL YR : ℤ)
    (hL : (XL : ℤ) ≡ (YL : ℤ) [ZMOD (q : ℤ) * movingSpectatorDenominator value T])
    (hR : (XR : ℤ) ≡ (YR : ℤ) [ZMOD (q : ℤ) * movingSpectatorDenominator value T]) :
    movingSignedSpectator value g D T XL XR = movingSignedSpectator value g D T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular =>
    simp only [movingSpectatorDenominator, mul_one] at hL hR
    have hl : (XL : ZMod q) = (YL : ZMod q) := by
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ q).mpr hL
    have hr : (XR : ZMod q) = (YR : ZMod q) := by
      exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ q).mpr hR
    simp only [movingSignedSpectator, Int.cast_mul, Int.cast_natCast, hl, hr]
  | node s CL CR U left right ihL ihR =>
    let c : ℤ := s * (MovingSlotReversal.naturalProduct value U : ℤ)
    let dl := movingSpectatorDenominator value left
    let dr := movingSpectatorDenominator value right
    let step := MovingSlotData.step s CL CR U left right false
    let p := step.signedPivot value XL XR
    let r := step.signedPivot value YL YR
    have hL' : (XL : ℤ) ≡ (YL : ℤ) [ZMOD c * ((q : ℤ) * dl * dr)] := by
      convert hL using 1
      dsimp [c, dl, dr, movingSpectatorDenominator]
      ring
    have hR' : (XR : ℤ) ≡ (YR : ℤ) [ZMOD c * ((q : ℤ) * dl * dr)] := by
      convert hR using 1
      dsimp [c, dl, dr, movingSpectatorDenominator]
      ring
    have hp : (p : ℤ) ≡ (r : ℤ) [ZMOD (q : ℤ) * dl * dr] :=
      step.signedPivot_modEq value hvalue hf.1 XL XR YL YR _ hL' hR'
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
    have hl := ihL hf.2.1 p XL r YL hpl hll
    have hr := ihR hf.2.2 p XR r YR hpr hrr
    change (if (p : ZMod q) = 0 then 0 else
      movingSignedSpectator value g D left p XL * star (movingSignedSpectator value g D right p XR)) =
      (if (r : ZMod q) = 0 then 0 else
      movingSignedSpectator value g D left r YL * star (movingSignedSpectator value g D right r YR))
    rw [hpq, hl, hr]

theorem movingSlotSpectator_eq_residue {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hI : T.Integral value XL XR)
    (hM : (q : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    movingSlotSpectator value g D T XL XR = movingSignedSpectator value g D T a b := by
  rw [← movingSignedSpectator_nat value hvalue g D T hf XL XR hI]
  exact movingSignedSpectator_modEq value hvalue g D T hf XL XR a b
    (hL.of_dvd hM) (hR.of_dvd hM)

theorem movingSignedSpectator_norm {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ z, ‖g z‖ ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) :
    ‖movingSignedSpectator value g D T XL XR‖ ≤ B ^ (2 ^ n) := by
  induction T generalizing XL XR with
  | leaf s regular => simpa only [movingSignedSpectator, pow_zero, pow_one] using hg _
  | @node n s CL CR U left right ihL ihR =>
    rw [movingSignedSpectator]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hB (2 ^ (n + 1))
    · rw [norm_mul, norm_star]
      calc
        _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
          mul_le_mul (ihL _ _) (ihR _ _) (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
