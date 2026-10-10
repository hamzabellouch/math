import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyFormulaGate

namespace OAI

/-! # Spectator evaluation without internal primes in the period

At a spectator prime the entire reversal denominator is a unit. The field
recursion therefore depends only on the two spectator residues, even though
the original recursion used integer division by compensation products.
-/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.modularPivot {σ : Type*} (step : MovingSlotReversal σ)
    (value : σ → ℕ) (q : ℕ) [Fact q.Prime] (x y : ZMod q) : ZMod q :=
  ((step.leftFrequency : ZMod q) * (y * MovingSlotReversal.naturalProduct value step.rightSlots) -
    (step.rightFrequency : ZMod q) * (x * MovingSlotReversal.naturalProduct value step.leftSlots)) /
      ((step.rootFrequency : ZMod q) * MovingSlotReversal.naturalProduct value step.compensationSlots)

def MovingSlotData.ModularDenominators {σ : Type*} (value : σ → ℕ) (q : ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node s _ _ U left right =>
      (s : ZMod q) ≠ 0 ∧ (MovingSlotReversal.naturalProduct value U : ZMod q) ≠ 0 ∧
        left.ModularDenominators value q ∧ right.ModularDenominators value q

theorem MovingSlotData.modularDenominators_of_units {σ : Type*}
    (value : σ → ℕ) (q : ℕ) [Fact q.Prime] (hvalue : ∀ i, (value i : ZMod q) ≠ 0)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (fun s => (s : ZMod q) ≠ 0)) :
    T.ModularDenominators value q := by
  induction T with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    refine ⟨hf.1, ?_, ihL hf.2.1, ihR hf.2.2⟩
    have hp : (U.map fun i => (value i : ZMod q)).prod ≠ 0 := by
      apply List.prod_ne_zero
      intro hz
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hz
      exact hvalue i hi
    simpa only [MovingSlotReversal.naturalProduct, Nat.cast_list_prod,
      List.map_map, Function.comp_def] using hp

theorem MovingSlotReversal.modularPivot_of_signedIntegral {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (q : ℕ) [Fact q.Prime]
    (hs : (step.rootFrequency : ZMod q) ≠ 0)
    (hu : (MovingSlotReversal.naturalProduct value step.compensationSlots : ZMod q) ≠ 0)
    (x y : ℤ) (hI : step.SignedIntegralAt value x y) :
    step.modularPivot value q x y = (step.signedPivot value x y : ZMod q) := by
  have he := congrArg (fun z : ℤ => (z : ZMod q)) hI
  simp only [MovingSlotReversal.signedNumerator,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast] at he
  unfold modularPivot
  apply (div_eq_iff (mul_ne_zero hs hu)).mpr
  linear_combination he

noncomputable def movingModularSpectator {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    {n : ℕ} → MovingSlotData σ n → ZMod q → ZMod q → ℂ
  | _, .leaf s regular, x, y =>
      g ((s : ZMod q) / ((D : ZMod q) * (x * y * MovingSlotReversal.naturalProduct value regular)))
  | _, .node s CL CR U left right, x, y =>
      let p := (MovingSlotData.step s CL CR U left right false).modularPivot value q x y
      if p = 0 then 0 else
        movingModularSpectator value q g D left p x * star (movingModularSpectator value q g D right p y)

theorem movingSignedSpectator_eq_modular {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (hden : T.ModularDenominators value q)
    (x y : ℤ) (hI : T.SignedIntegral value x y) :
    movingSignedSpectator value g D T x y = movingModularSpectator value q g D T x y := by
  induction T generalizing x y with
  | leaf => simp only [movingSignedSpectator, movingModularSpectator, Int.cast_mul, Int.cast_natCast]
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedSpectator, movingModularSpectator,
      (MovingSlotData.step s CL CR U left right false).modularPivot_of_signedIntegral
        value q hden.1 hden.2.1 x y hI.1]
    split_ifs
    · rfl
    · rw [ihL hden.2.2.1 _ _ hI.2.1, ihR hden.2.2.2 _ _ hI.2.2]

theorem movingModularSpectator_norm {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ z, ‖g z‖ ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q) :
    ‖movingModularSpectator value q g D T x y‖ ≤ B ^ (2 ^ n) := by
  induction T generalizing x y with
  | leaf => simpa only [movingModularSpectator, pow_zero, pow_one] using hg _
  | @node n s CL CR U left right ihL ihR =>
    rw [movingModularSpectator]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hB (2 ^ (n + 1))
    · rw [norm_mul, norm_star]
      calc
        _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
          mul_le_mul (ihL _ _) (ihR _ _) (norm_nonneg _) (pow_nonneg hB _)
        _ = B ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

end Ostmann

end OAI
