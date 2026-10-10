import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeLineGate

namespace OAI

/-! # Exact frequency and internal-prime splitting before real restrictions

All divisions here are integer divisions. Positivity is deliberately left to
the existing real gate. The equivalence recovers integer divisibility from
the two disjoint residue blocks, including at every descendant node.
-/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.SignedIntegralAt {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (x y : ℤ) : Prop :=
  s.signedNumerator value x y =
    s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ) * s.signedPivot value x y

def MovingSlotData.SignedIntegral {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR U left right, x, y =>
      let step := MovingSlotData.step s CL CR U left right false
      let p := step.signedPivot value x y
      step.SignedIntegralAt value x y ∧ left.SignedIntegral value p x ∧ right.SignedIntegral value p y

def movingSignedFrequencyUnits {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, T@(.leaf _ _), x, y => movingFrequencyLocalUnits T x y
  | _, T@(.node s CL CR U left right), x, y =>
      let p := (MovingSlotData.step s CL CR U left right false).signedPivot value x y
      movingFrequencyLocalUnits T x y ∧
        movingSignedFrequencyUnits value left p x ∧ movingSignedFrequencyUnits value right p y

theorem movingSignedFrequencyUnits_auxiliary {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) :
    movingSignedFrequencyUnits value T x y ↔ movingSignedAuxiliaryUnits value [] T x y := by
  induction T generalizing x y with
  | leaf => simp only [movingSignedFrequencyUnits, movingSignedAuxiliaryUnits,
      movingFrequencyLocalUnits, movingAuxiliaryLocalUnits, List.prod_nil, Nat.cast_one,
      isCoprime_one_right, and_true]
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedFrequencyUnits, movingSignedAuxiliaryUnits,
      movingFrequencyLocalUnits, movingAuxiliaryLocalUnits, List.prod_nil, Nat.cast_one,
      isCoprime_one_right, and_true, ihL, ihR]

theorem MovingSlotReversal.frequencyPivot_signed_modEq {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (R : ℤ) (k : ℕ)
    (hs : s.rootFrequency ≠ 0)
    (hu : IsCoprime (naturalProduct value s.compensationSlots : ℤ) R)
    (x y : ℤ) (hI : s.SignedIntegralAt value x y) :
    s.frequencyPivot value R k x y ≡ s.signedPivot value x y [ZMOD R ^ k] := by
  unfold frequencyPivot
  rw [show s.signedNumerator value x y = s.rootFrequency *
      ((naturalProduct value s.compensationSlots : ℤ) * s.signedPivot value x y) by
    simpa only [SignedIntegralAt, mul_assoc] using hI]
  rw [Int.mul_ediv_cancel_left _ hs]
  simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using
    (coprime_bezout_inverse_modEq _ R hu k).mul_right (s.signedPivot value x y)

theorem pairwise_coprime_list_prod_int_dvd_iff (U : List ℕ)
    (hU : U.Pairwise Nat.Coprime) (N : ℤ) :
    (U.prod : ℤ) ∣ N ↔ ∀ b ∈ U, (b : ℤ) ∣ N := by
  simp only [Int.natCast_dvd, pairwise_coprime_list_prod_dvd_iff U hU]

theorem MovingSlotReversal.signedIntegral_of_prime_lines {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (R : ℤ)
    (hsR : s.rootFrequency ∣ R)
    (hu : IsCoprime (naturalProduct value s.compensationSlots : ℤ) R)
    (hp : (s.compensationSlots.map value).Pairwise Nat.Coprime) (x y : ℤ)
    (hs : s.rootFrequency ∣ s.signedNumerator value x y)
    (hlines : ∀ i ∈ s.compensationSlots, (value i : ℤ) ∣ s.signedNumerator value x y) :
    s.SignedIntegralAt value x y := by
  have hU : (naturalProduct value s.compensationSlots : ℤ) ∣ s.signedNumerator value x y := by
    apply (pairwise_coprime_list_prod_int_dvd_iff _ hp _).mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hlines i hi
  have hc : IsCoprime s.rootFrequency (naturalProduct value s.compensationSlots : ℤ) :=
    (hu.of_isCoprime_of_dvd_right hsR).symm
  have hd := hc.mul_dvd hs hU
  exact (Int.mul_ediv_cancel' hd).symm

/-- The frequency block and the simultaneous prime lines give precisely
the original signed integer recursion with its subtree-frequency unit tests.
This is an equivalence on every top pair, before the real support is imposed. -/
theorem moving_frequency_internal_split {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j) (R : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) R)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hf : T.Frequencies (· ≠ 0))
    (hfmod : ∀ i, T.Frequencies (fun f => (f : ZMod (value i)) ≠ 0))
    (hR : T.frequencyProduct ∣ R) (hdistinct : T.CompensationDistinct value) (x y : ℤ) :
    movingFrequencyGate value R T x y ∧ movingPrimeLineSupport value T x y ↔
      T.SignedIntegral value x y ∧ movingSignedFrequencyUnits value T x y := by
  induction T generalizing x y with
  | leaf s C =>
    simp only [movingFrequencyGate, MovingSlotData.SignedIntegral, movingSignedFrequencyUnits,
      movingPrimeLineSupport, MovingSlotData.occurrences, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, true_and]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right false
    let p := step.signedPivot value x y
    let r := step.frequencyPivot value R (n + 1) x y
    have hd := MovingSlotData.frequencyProduct_node_dvd s CL CR U left right R hR
    have hU : IsCoprime (MovingSlotReversal.naturalProduct value U : ℤ) R :=
      movingNaturalProduct_coprime value U R (fun i _ => hsmall i)
    have hstep (hI : step.SignedIntegralAt value x y) :
        movingFrequencyGate value R left r x ↔ movingFrequencyGate value R left p x := by
      exact movingFrequencyGate_modEq value R left hf.2.1 hd.2.1 r x p x
        (step.frequencyPivot_signed_modEq value R (n + 1) hf.1 hU x y hI) (Int.ModEq.refl _)
    have hstepR (hI : step.SignedIntegralAt value x y) :
        movingFrequencyGate value R right r y ↔ movingFrequencyGate value R right p y := by
      exact movingFrequencyGate_modEq value R right hf.2.2 hd.2.2 r y p y
        (step.frequencyPivot_signed_modEq value R (n + 1) hf.1 hU x y hI) (Int.ModEq.refl _)
    have hline (hI : step.SignedIntegralAt value x y) :=
      movingPrimeLineSupport_node_of_levels tier value hprime hdisjoint s CL CR U left right
        hlevels hfmod x y p hI
    have hl := ihL hlevels.2.2.2.1 hf.2.1 (fun i => (hfmod i).2.1) hd.2.1 hdistinct.2.1 p x
    have hr := ihR hlevels.2.2.2.2 hf.2.2 (fun i => (hfmod i).2.2) hd.2.2 hdistinct.2.2 p y
    constructor
    · rintro ⟨hfreq, hlines⟩
      have hroot := movingPrimeLineSupport_root value s CL CR U left right x y hlines
      have hI : step.SignedIntegralAt value x y :=
        step.signedIntegral_of_prime_lines value R hd.1 hU hdistinct.1 x y hfreq.2.1 hroot
      have hlines' := (hline hI).mp hlines
      have hL := hl.mp ⟨(hstep hI).mp hfreq.2.2.1, hlines'.2.1⟩
      have hR := hr.mp ⟨(hstepR hI).mp hfreq.2.2.2, hlines'.2.2⟩
      exact ⟨⟨hI, hL.1, hR.1⟩, hfreq.1, hL.2, hR.2⟩
    · rintro ⟨⟨hI, hIL, hIR⟩, hunit, hUL, hUR⟩
      have hL := hl.mpr ⟨hIL, hUL⟩
      have hR := hr.mpr ⟨hIR, hUR⟩
      have hdiv : s ∣ step.signedNumerator value x y :=
        ⟨_, by simpa only [MovingSlotReversal.SignedIntegralAt, step,
          MovingSlotData.step, mul_assoc] using hI⟩
      have hroot : ∀ i ∈ U, (value i : ℤ) ∣ step.signedNumerator value x y := by
        intro i hi
        have hp : value i ∣ MovingSlotReversal.naturalProduct value U :=
          List.dvd_prod (List.mem_map.mpr ⟨i, hi, rfl⟩)
        rw [hI]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hp) _) _
      exact ⟨⟨hunit, hdiv, (hstep hI).mpr hL.1, (hstepR hI).mpr hR.1⟩,
        (hline hI).mpr ⟨hroot, hL.2, hR.2⟩⟩

end Ostmann

end OAI
