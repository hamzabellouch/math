import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSpectatorUnits
import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueCoprime
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkFrozen
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The actual separated prime ranges imply all spectator unit tests -/

namespace Ostmann
open Filter
open scoped Classical

theorem prime_cast_ne_zero_of_lt {q : ℕ} [Fact q.Prime] (p : ℕ) (hp : p.Prime)
    (hqp : q < p) : (p : ZMod q) ≠ 0 := by
  apply IsUnit.ne_zero
  apply (ZMod.isUnit_iff_coprime p q).mpr
  exact (Nat.coprime_primes hp (Fact.out : q.Prime)).mpr (Ne.symm (ne_of_lt hqp))

/-- The spectator primes are far smaller than every original nongiant
prime. This supplies the small-word and internal-sample unit tests for each
pattern without any restriction on their actual residue values. -/
theorem movingPattern_spectator_units_of_ranges {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (hsmall : ∀ b, ∀ j ∈ flattenMovingSlots n (small b), j ∉ Set.range slot)
    (base : Fin (N + 1) → ℕ)
    (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
    (L : ℝ) (hL : 0 < L) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (hp : ∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L)))
    (hlarge : ∀ j, j ∉ Set.range (movingPatternBulkEmbedding e slot) →
      Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (base j : ℝ)) :
    (∀ i b, ∀ j ∈ flattenMovingSlots n (small b),
      (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0) ∧
    (∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0) := by
  have hunits (i : Fin m) (j : Fin (N + 1))
      (hj : j ∉ Set.range (movingPatternBulkEmbedding e slot)) :
      (base j : ZMod (p i)) ≠ 0 := by
    apply prime_cast_ne_zero_of_lt _ (hbase j hj)
    have hlt : (p i : ℝ) < base j := (hp i).trans_lt ((Real.exp_lt_exp.mpr
      (Real.exp_lt_exp.mpr (by nlinarith))).trans_le (hlarge j hj))
    exact_mod_cast hlt
  constructor
  · intro i b j hj
    apply hunits
    rintro ⟨k, hk⟩
    apply hsmall b j hj
    refine ⟨k, ?_⟩
    exact Sum.inl.inj (e.symm.injective hk)
  · intro i c
    exact hunits i _ (movingPatternBulkEmbedding_internal_absent e slot c)

/-- The original finite Fourier cutoff lies below every selected spectator
prime, uniformly in the linear bulk length. -/
theorem moving_spectator_frequency_range (k : ℕ) (A a : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B : ℕ) (p : Fin m → ℕ), (B : ℝ) ≤ Real.exp (A * m) →
      (∀ i, Real.exp (Real.exp (a * L)) ≤ (p i : ℝ)) →
      ∀ s : ℤ, s.natAbs ≤ B → ∀ i, s.natAbs < p i := by
  filter_upwards [frequency_modulus_lt_spectators A ((k : ℝ) ^ 4) a hA (by positivity) ha,
    eventually_ge_atTop (0 : ℝ)] with L hlt hL
  dsimp only
  intro B p hB hp s hs i
  exact hs.trans_lt (hlt _ B p (spectatorBulkCount_upper k L hL) hB hp i)

end Ostmann

end OAI
