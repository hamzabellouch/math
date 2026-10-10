import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationLines
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAuxiliaryPeriod

namespace OAI

/-! # Frequency residues with compensation factors inverted

Unlike the signed integer recursion, this recursion divides only by the
frequency. Compensation factors are inverted modulo a frequency power, so
no internal prime enters its period. One power is consumed per reversal.
-/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.signedNumerator {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (XL XR : ℤ) : ℤ :=
  s.leftFrequency * (XR * (naturalProduct value s.rightSlots : ℤ)) -
    s.rightFrequency * (XL * (naturalProduct value s.leftSlots : ℤ))

def MovingSlotReversal.frequencyPivot {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (R : ℤ) (k : ℕ) (XL XR : ℤ) : ℤ :=
  (s.signedNumerator value XL XR / s.rootFrequency) *
    Int.gcdA (naturalProduct value s.compensationSlots : ℤ) (R ^ k)

theorem coprime_bezout_inverse_modEq (u R : ℤ) (hu : IsCoprime u R) (k : ℕ) :
    u * Int.gcdA u (R ^ k) ≡ 1 [ZMOD R ^ k] := by
  have h := Int.gcd_eq_gcd_ab u (R ^ k)
  have hg : Int.gcd u (R ^ k) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hu.pow_right
  rw [hg] at h
  apply Int.modEq_iff_dvd.mpr
  refine ⟨Int.gcdB u (R ^ k), ?_⟩
  linear_combination h

theorem MovingSlotReversal.signedNumerator_modEq {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (XL XR YL YR M : ℤ)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    s.signedNumerator value XL XR ≡ s.signedNumerator value YL YR [ZMOD M] :=
  ((hR.mul_right _).mul_left _).sub ((hL.mul_right _).mul_left _)

theorem MovingSlotReversal.frequencyPivot_modEq {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (R : ℤ) (k : ℕ) (hs : s.rootFrequency ≠ 0)
    (hsR : s.rootFrequency ∣ R) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD R ^ (k + 1)]) (hR : XR ≡ YR [ZMOD R ^ (k + 1)]) :
    s.frequencyPivot value R k XL XR ≡ s.frequencyPivot value R k YL YR [ZMOD R ^ k] := by
  have hd : s.rootFrequency * R ^ k ∣ R ^ (k + 1) := by
    simpa only [pow_succ, mul_comm] using mul_dvd_mul hsR (dvd_refl (R ^ k))
  exact (int_modEq_ediv _ _ _ _ hs
    ((s.signedNumerator_modEq value XL XR YL YR _ hL hR).of_dvd hd)).mul_right _

theorem MovingSlotReversal.frequencyPivot_nat_modEq {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (R : ℤ) (k : ℕ) (hs : s.rootFrequency ≠ 0)
    (hu : IsCoprime (naturalProduct value s.compensationSlots : ℤ) R)
    (XL XR : ℕ) (hI : s.IntegralAt value (XL, XR)) :
    s.frequencyPivot value R k XL XR ≡ (s.naturalPivot value XL XR : ℤ) [ZMOD R ^ k] := by
  have hn : s.signedNumerator value XL XR = s.rootFrequency *
      ((naturalProduct value s.compensationSlots : ℤ) * s.naturalPivot value XL XR) := by
    simpa only [signedNumerator, Nat.cast_mul] using hI.2
  unfold frequencyPivot
  rw [hn, Int.mul_ediv_cancel_left _ hs]
  have h := (coprime_bezout_inverse_modEq _ R hu k).mul_right
    (s.naturalPivot value XL XR : ℤ)
  simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using h

def movingFrequencyLocalUnits {σ : Type*} {n : ℕ} (T : MovingSlotData σ n)
    (XL XR : ℤ) : Prop :=
  IsCoprime XL T.frequencyProduct ∧ IsCoprime XR T.frequencyProduct

def movingFrequencyGate {σ : Type*} (value : σ → ℕ) (R : ℤ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, T@(.leaf _ _), XL, XR => movingFrequencyLocalUnits T XL XR
  | n + 1, T@(.node s CL CR U left right), XL, XR =>
      let step := MovingSlotData.step s CL CR U left right false
      let p := step.frequencyPivot value R (n + 1) XL XR
      movingFrequencyLocalUnits T XL XR ∧ s ∣ step.signedNumerator value XL XR ∧
        movingFrequencyGate value R left p XL ∧ movingFrequencyGate value R right p XR

theorem movingFrequencyLocalUnits_modEq {σ : Type*} {n : ℕ} (T : MovingSlotData σ n)
    (XL XR YL YR M : ℤ) (hM : T.frequencyProduct ∣ M)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    movingFrequencyLocalUnits T XL XR ↔ movingFrequencyLocalUnits T YL YR := by
  exact and_congr (int_modEq_isCoprime_iff (hL.of_dvd hM))
    (int_modEq_isCoprime_iff (hR.of_dvd hM))

theorem MovingSlotData.frequencyProduct_node_dvd {σ : Type*} {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (R : ℤ)
    (h : (MovingSlotData.node s CL CR U left right).frequencyProduct ∣ R) :
    s ∣ R ∧ left.frequencyProduct ∣ R ∧ right.frequencyProduct ∣ R := by
  refine ⟨?_, ?_, ?_⟩
  · exact dvd_trans ⟨left.frequencyProduct * right.frequencyProduct, by
      simp only [frequencyProduct]; ring⟩ h
  · exact dvd_trans ⟨s * right.frequencyProduct, by
      simp only [frequencyProduct]; ring⟩ h
  · exact (dvd_mul_left _ _).trans h

/-- The entire frequency block has a period containing only frequencies.
The compensation primes have disappeared from the period. -/
theorem movingFrequencyGate_modEq {σ : Type*} (value : σ → ℕ) (R : ℤ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hR : T.frequencyProduct ∣ R) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD R ^ (n + 1)]) (hRight : XR ≡ YR [ZMOD R ^ (n + 1)]) :
    movingFrequencyGate value R T XL XR ↔ movingFrequencyGate value R T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular =>
    exact movingFrequencyLocalUnits_modEq _ _ _ _ _ _
      (by simpa using hR) hL hRight
  | @node n s CL CR U left right ihL ihR =>
    have hd := MovingSlotData.frequencyProduct_node_dvd s CL CR U left right R hR
    have hp := (MovingSlotData.step s CL CR U left right false).frequencyPivot_modEq
      value R (n + 1) hf.1 hd.1 XL XR YL YR hL hRight
    have hpow : R ∣ R ^ (n + 1 + 1) := dvd_pow_self R (by omega)
    have hnum := (MovingSlotData.step s CL CR U left right false).signedNumerator_modEq
      value XL XR YL YR _ hL hRight
    have hdiv : s ∣ (MovingSlotData.step s CL CR U left right false).signedNumerator value XL XR ↔
        s ∣ (MovingSlotData.step s CL CR U left right false).signedNumerator value YL YR :=
      (hnum.of_dvd (hd.1.trans hpow)).dvd_iff
    have hlocal := movingFrequencyLocalUnits_modEq
      (MovingSlotData.node s CL CR U left right) XL XR YL YR _ (hR.trans hpow) hL hRight
    change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
    exact and_congr hlocal (and_congr hdiv (and_congr
      (ihL hf.2.1 hd.2.1 _ _ _ _ hp (hL.of_dvd (pow_dvd_pow R (by omega))))
      (ihR hf.2.2 hd.2.2 _ _ _ _ hp (hRight.of_dvd (pow_dvd_pow R (by omega))))))

theorem movingNaturalProduct_coprime {σ : Type*} (value : σ → ℕ) (slots : List σ)
    (R : ℤ) (h : ∀ i ∈ slots, IsCoprime (value i : ℤ) R) :
    IsCoprime (MovingSlotReversal.naturalProduct value slots : ℤ) R := by
  induction slots with
  | nil => simpa [MovingSlotReversal.naturalProduct] using (isCoprime_one_left (x := R))
  | cons i slots ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons, Nat.cast_mul] using
      (h i List.mem_cons_self).mul_left (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

/-- On an original integral history this frequency-only recursion is exactly
the original subtree-frequency unit support. No stronger giant unit test is
inserted and all frequency divisibility tests remain in the new recursion. -/
theorem movingFrequencyGate_nat_iff {σ : Type*} (value : σ → ℕ) (R : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) R)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hR : T.frequencyProduct ∣ R) (XL XR : ℕ) (hI : T.Integral value XL XR) :
    movingFrequencyGate value R T XL XR ↔ movingAuxiliaryUnits value [] T XL XR := by
  induction T generalizing XL XR with
  | leaf s regular =>
    simp only [movingFrequencyGate, movingFrequencyLocalUnits, movingAuxiliaryUnits,
      movingAuxiliaryLocalUnits, List.prod_nil, Nat.cast_one, isCoprime_one_right, and_true]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right false
    let p := step.naturalPivot value XL XR
    let r := step.frequencyPivot value R (n + 1) XL XR
    have hd := MovingSlotData.frequencyProduct_node_dvd s CL CR U left right R hR
    have hp : r ≡ (p : ℤ) [ZMOD R ^ (n + 1)] :=
      step.frequencyPivot_nat_modEq value R (n + 1) hf.1
        (movingNaturalProduct_coprime value U R (fun i _ => hsmall i)) XL XR hI.1
    have hl := movingFrequencyGate_modEq value R left hf.2.1 hd.2.1 r XL p XL hp (Int.ModEq.refl _)
    have hr := movingFrequencyGate_modEq value R right hf.2.2 hd.2.2 r XR p XR hp (Int.ModEq.refl _)
    have hn : s ∣ step.signedNumerator value XL XR := by
      have h := hI.1.2
      exact ⟨_, by simpa only [step, MovingSlotReversal.signedNumerator,
        MovingSlotData.step, Nat.cast_mul] using h⟩
    change (movingFrequencyLocalUnits _ _ _ ∧ s ∣ step.signedNumerator value XL XR ∧
      movingFrequencyGate value R left r XL ∧ movingFrequencyGate value R right r XR) ↔ _
    rw [hl, hr, ihL hf.2.1 hd.2.1 p XL hI.2.1, ihR hf.2.2 hd.2.2 p XR hI.2.2]
    simp only [movingAuxiliaryUnits, movingAuxiliaryLocalUnits, movingFrequencyLocalUnits,
      List.prod_nil, Nat.cast_one, isCoprime_one_right, and_true, hn, true_and]
    rfl

end Ostmann

end OAI
