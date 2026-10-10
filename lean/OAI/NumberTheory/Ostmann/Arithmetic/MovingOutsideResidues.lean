import OAI.NumberTheory.Ostmann.Arithmetic.MovingModularSpectator

namespace OAI

/-! # Outside giant-unit tests in spectator coordinates -/

namespace Ostmann
open scoped Classical

def movingSignedOutsideUnits {σ : Type*} (value : σ → ℕ) (M : ℤ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, .leaf _ _, x, y => IsCoprime x M ∧ IsCoprime y M
  | _, .node s CL CR U left right, x, y =>
      let p := (MovingSlotData.step s CL CR U left right false).signedPivot value x y
      (IsCoprime x M ∧ IsCoprime y M) ∧
        movingSignedOutsideUnits value M left p x ∧ movingSignedOutsideUnits value M right p y

theorem movingSignedAuxiliaryUnits_split {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) :
    movingSignedAuxiliaryUnits value outside T x y ↔
      movingSignedFrequencyUnits value T x y ∧ movingSignedOutsideUnits value outside.prod T x y := by
  induction T generalizing x y with
  | leaf =>
    simp only [movingSignedAuxiliaryUnits, movingSignedFrequencyUnits,
      movingSignedOutsideUnits, movingAuxiliaryLocalUnits, movingFrequencyLocalUnits]
    tauto
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedAuxiliaryUnits, movingSignedFrequencyUnits,
      movingSignedOutsideUnits, movingAuxiliaryLocalUnits, movingFrequencyLocalUnits, ihL, ihR]
    tauto

def movingModularGiantUnits {σ : Type*} (value : σ → ℕ) (q : ℕ) [Fact q.Prime] :
    {n : ℕ} → MovingSlotData σ n → ZMod q → ZMod q → Prop
  | _, .leaf _ _, x, y => x ≠ 0 ∧ y ≠ 0
  | _, .node s CL CR U left right, x, y =>
      let p := (MovingSlotData.step s CL CR U left right false).modularPivot value q x y
      (x ≠ 0 ∧ y ≠ 0) ∧
        movingModularGiantUnits value q left p x ∧ movingModularGiantUnits value q right p y

theorem movingModularGiantUnits_local {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q)
    (h : movingModularGiantUnits value q T x y) : x ≠ 0 ∧ y ≠ 0 := by
  cases T with
  | leaf => exact h
  | node => exact h.1

theorem movingSignedOutsideUnits_modular {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] {n : ℕ} (T : MovingSlotData σ n)
    (hden : T.ModularDenominators value q) (x y : ℤ) (hI : T.SignedIntegral value x y) :
    movingSignedOutsideUnits value q T x y ↔ movingModularGiantUnits value q T x y := by
  have hlocal (z : ℤ) : IsCoprime z (q : ℤ) ↔ (z : ZMod q) ≠ 0 := by
    rw [isCoprime_comm, ← ZMod.coe_int_isUnit_iff_isCoprime, isUnit_iff_ne_zero]
  induction T generalizing x y with
  | leaf => exact and_congr (hlocal x) (hlocal y)
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedOutsideUnits, movingModularGiantUnits,
      (MovingSlotData.step s CL CR U left right false).modularPivot_of_signedIntegral
        value q hden.1 hden.2.1 x y hI.1, hlocal,
      ihL hden.2.2.1 _ _ hI.2.1, ihR hden.2.2.2 _ _ hI.2.2]

/-- With the original zero convention, a nonzero spectator coefficient
already enforces every outside giant-unit test at that prime. -/
theorem movingModularSpectator_nonzero_units {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (hg0 : g 0 = 0)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q)
    (h : movingModularSpectator value q g D T x y ≠ 0) :
    movingModularGiantUnits value q T x y := by
  induction T generalizing x y with
  | leaf s C =>
    constructor
    · intro hx
      exact h (by simp [movingModularSpectator, hx, hg0])
    · intro hy
      exact h (by simp [movingModularSpectator, hy, hg0])
  | node s CL CR U left right ihL ihR =>
    let p := (MovingSlotData.step s CL CR U left right false).modularPivot value q x y
    have hp : p ≠ 0 := by
      intro hp
      exact h (by simp only [movingModularSpectator, p, hp, ite_true])
    have hm : movingModularSpectator value q g D left p x *
        star (movingModularSpectator value q g D right p y) ≠ 0 := by
      simpa only [movingModularSpectator, show
        (MovingSlotData.step s CL CR U left right false).modularPivot value q x y ≠ 0 from hp,
        ite_false] using h
    have hl := ihL p x (mul_ne_zero_iff.mp hm).1
    have hr := ihR p y (by
      intro hz
      exact (mul_ne_zero_iff.mp hm).2 (by rw [hz, star_zero]))
    exact ⟨⟨(movingModularGiantUnits_local value q left p x hl).2,
      (movingModularGiantUnits_local value q right p y hr).2⟩, hl, hr⟩

theorem movingSignedOutsideUnits_mul {σ : Type*} (value : σ → ℕ) (M N : ℤ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) :
    movingSignedOutsideUnits value (M * N) T x y ↔
      movingSignedOutsideUnits value M T x y ∧ movingSignedOutsideUnits value N T x y := by
  induction T generalizing x y with
  | leaf => simp only [movingSignedOutsideUnits, IsCoprime.mul_right_iff]; tauto
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedOutsideUnits, IsCoprime.mul_right_iff, ihL, ihR]
    tauto

theorem movingSignedOutsideUnits_one {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) : movingSignedOutsideUnits value 1 T x y := by
  induction T generalizing x y with
  | leaf => exact ⟨isCoprime_one_right, isCoprime_one_right⟩
  | node s CL CR U left right ihL ihR =>
    exact ⟨⟨isCoprime_one_right, isCoprime_one_right⟩, ihL _ _, ihR _ _⟩

theorem movingSignedOutsideUnits_list {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) :
    movingSignedOutsideUnits value (outside.prod : ℤ) T x y ↔
      ∀ q ∈ outside, movingSignedOutsideUnits value (q : ℤ) T x y := by
  induction outside with
  | nil => simp only [List.prod_nil, Nat.cast_one, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, iff_true]; exact movingSignedOutsideUnits_one value T x y
  | cons q outside ih =>
    simp only [List.prod_cons, Nat.cast_mul, movingSignedOutsideUnits_mul, ih,
      List.forall_mem_cons]

theorem movingModularSpectatorProduct_outside_units {σ I : Type*}
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (hg0 : ∀ i ∈ S, g i 0 = 0) (outside : List ℕ)
    (hcover : ∀ p ∈ outside, ∃ i ∈ S, q i = p)
    {n : ℕ} (T : MovingSlotData σ n) (hden : ∀ i ∈ S, T.ModularDenominators value (q i))
    (x y : ℤ) (hI : T.SignedIntegral value x y)
    (hz : (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T x y) ≠ 0) :
    movingSignedOutsideUnits value (outside.prod : ℤ) T x y := by
  apply (movingSignedOutsideUnits_list value outside T x y).mpr
  intro p hp
  obtain ⟨i, hi, rfl⟩ := hcover p hp
  apply (movingSignedOutsideUnits_modular value (q i) T (hden i hi) x y hI).mpr
  apply movingModularSpectator_nonzero_units value (q i) (g i) (D i) (hg0 i hi) T x y
  exact (Finset.prod_ne_zero_iff.mp hz) i hi

end Ostmann

end OAI
