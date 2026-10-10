import OAI.NumberTheory.Ostmann.Construction.SupportedPrimePrior
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPriorSupport

namespace OAI

/-! # Concrete support conditions for the original harmonic role priors -/

namespace Ostmann
open scoped Classical BigOperators

theorem harmonic_product_mem {N : ℕ} (P : Finset ℕ)
    (Q : Fin (N + 1) → Finset ℕ) (x : Fin (N + 1) → P)
    (hx : productPrior (fun i => primeSubsetPrior P (Q i)) x ≠ 0) :
    ∀ i, (x i : ℕ) ∈ Q i := by
  intro i
  exact primeSubsetPrior_support P (Q i) (x i)
    ((Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i))

theorem harmonic_product_distinct_levels {N : ℕ} (P : Finset ℕ)
    (Q : Fin (N + 1) → Finset ℕ) (tier : Fin (N + 1) → ℕ)
    (hQ : ∀ i j, tier i ≠ tier j → Disjoint (Q i) (Q j))
    (x : Fin (N + 1) → P)
    (hx : productPrior (fun i => primeSubsetPrior P (Q i)) x ≠ 0) :
    ∀ i j, tier i ≠ tier j → (x i : ℕ) ≠ (x j : ℕ) := by
  intro i j hij heq
  have hm := harmonic_product_mem P Q x hx
  exact Finset.disjoint_left.mp (hQ i j hij) (hm i) (heq ▸ hm j)

/-- The original internal samples lie strictly below the external tier.
Thus the same disjoint shell choice supplies the cross-coordinate condition. -/
theorem harmonic_product_external_internal {B C : Type*} {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (hB : ∀ b, n ≤ tierB b)
    (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (P : Finset ℕ) (Q : Fin (N + 1) → Finset ℕ)
    (hQ : ∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
      Disjoint (Q i) (Q j)) (x : Fin (N + 1) → P)
    (hx : productPrior (fun i => primeSubsetPrior P (Q i)) x ≠ 0) :
    ∀ b c, (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ) := by
  intro b c
  apply harmonic_product_distinct_levels P Q (fun i => (Sum.elim tierB tierC) (e i)) hQ x hx
  simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
  have hc : tierC c < n := by
    have ht := htier (rep c).val
    rw [(rep c).property] at ht
    exact ht.trans_lt (movingSampleTier_lt (rep c).val.2)
  have hb := hB b
  omega

/-- A nonzero original frequency smaller than an internal prime remains
nonzero modulo that prime. -/
theorem intCast_ne_zero_of_natAbs_lt (q : ℕ) (s : ℤ) (hs : s ≠ 0)
    (hqs : s.natAbs < q) : (s : ZMod q) ≠ 0 := by
  intro hz
  have hd : q ∣ s.natAbs := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd s q).mp hz
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hh
  exact (not_le_of_gt hqs) (Nat.le_of_dvd (Int.natAbs_pos.mpr hs) hd)

theorem harmonic_product_frequency_units {N : ℕ} (P : Finset ℕ)
    (Q : Fin (N + 1) → Finset ℕ) (x : Fin (N + 1) → P)
    (hx : productPrior (fun i => primeSubsetPrior P (Q i)) x ≠ 0)
    (i : Fin (N + 1)) (s : ℤ) (hs : s ≠ 0)
    (hQ : ∀ q ∈ Q i, s.natAbs < q) : (s : ZMod (x i : ℕ)) ≠ 0 :=
  intCast_ne_zero_of_natAbs_lt _ s hs (hQ _ (harmonic_product_mem P Q x hx i))

end Ostmann

end OAI
