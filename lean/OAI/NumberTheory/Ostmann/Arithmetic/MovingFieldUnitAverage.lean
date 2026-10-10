import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedAverages
import OAI.NumberTheory.Ostmann.Characters.AffineAction

namespace OAI

/-! # Exact restriction of a spectator's mixed average to unit pairs -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingModularSpectator_zero {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (hg : g 0 = 0) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ZMod q) (hzero : x = 0 ∨ y = 0) :
    movingModularSpectator value q g D T x y = 0 := by
  induction T generalizing x y with
  | leaf s regular =>
    rcases hzero with h | h <;>
      simp only [movingModularSpectator, h, zero_mul, mul_zero, div_zero, hg]
  | node s CL CR U left right ihL ihR =>
    simp only [movingModularSpectator]
    split_ifs
    · rfl
    · rcases hzero with h | h
      · rw [ihL _ _ (Or.inr h), zero_mul]
      · rw [ihR _ _ (Or.inr h), star_zero, mul_zero]

theorem movingSpectatorHaarAverage_eq_units {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (hg : g 0 = 0) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) :
    movingSpectatorHaarAverage value q g D T =
      ((Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)) *
        ((Fintype.card ((ZMod q)ˣ × (ZMod q)ˣ) : ℂ)⁻¹ *
          ∑ z : (ZMod q)ˣ × (ZMod q)ˣ, movingSpectatorPairFactor value q g D T z.1 z.2) := by
  have hz (y : (ZMod q)ˣ) : movingSpectatorPairFactor value q g D T 0 y = 0 := by
    rw [movingSpectatorPairFactor, movingModularSpectator_zero value g hg (D false) (T false)
      0 y (Or.inl rfl), zero_mul]
  have hs : (∑ z : ZMod q × (ZMod q)ˣ, movingSpectatorPairFactor value q g D T z.1 z.2) =
      ∑ z : (ZMod q)ˣ × (ZMod q)ˣ, movingSpectatorPairFactor value q g D T z.1 z.2 := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun x y : (ZMod q)ˣ =>
      movingSpectatorPairFactor value q g D T x y)]
    apply Finset.sum_congr rfl
    intro y _
    exact (sum_units_eq_sum_of_zero (fun x => movingSpectatorPairFactor value q g D T x y) (hz y)).symm
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hu : (Fintype.card (ZMod q)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ZMod q)ˣ ≠ 0)
  simp only [movingSpectatorHaarAverage, hs, Fintype.card_prod, ZMod.card, Nat.cast_mul]
  field_simp

end Ostmann

end OAI
