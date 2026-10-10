import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicTransfer

namespace OAI

open Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open Ostmann.Dirichlet.PrimeCountAbel (logarithmicIntegral)
namespace Ostmann.Arithmetic.PrimeProgression

theorem isUnit_exists_coprime_int_rep {M : ℕ} (hM : 0 < M)
    (a : ZMod M) (ha : IsUnit a) :
    ∃ r : ℤ, (r : ZMod M) = a ∧ IsCoprime r (M : ℤ) := by
  let : NeZero M := ⟨Nat.ne_of_gt hM⟩
  refine ⟨(a.val : ℤ), ?_, ?_⟩
  · simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  · apply IsCoprime.symm
    apply (ZMod.coe_int_isUnit_iff_isCoprime (a.val : ℤ) M).mp
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using ha

theorem harmonic_estimate_units_of_count_estimate
    (hcount : ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ (M : ℕ) (r : ℤ), 0 < M → IsCoprime r (M : ℤ) →
      (M : ℝ) ≤ Real.exp (c * (Real.log X) ^ (1 / 3 : ℝ)) →
      |((Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 X M r).card : ℝ) -
        logarithmicIntegral X / (M.totient : ℝ)| ≤
        C * X * Real.exp (-c * (Real.log X) ^ (1 / 3 : ℝ))) :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧ ∀ lo hi : ℝ,
      L₀ ≤ lo → lo ≤ hi → hi - lo ≤ 1 → ∀ (N M : ℕ) (a : ZMod M),
      ⌊Real.exp hi⌋₊ ≤ N → 0 < M → IsUnit a →
      (M : ℝ) ≤ Real.exp (d * lo ^ (1 / 3 : ℝ)) →
      |harmonicProgression N M a lo hi - harmonicIntegral M lo hi| ≤
        K * Real.exp (-d * lo ^ (1 / 3 : ℝ)) := by
  obtain ⟨d, K, L₀, hd, hK, hL₀, h⟩ := harmonic_estimate_of_count_estimate hcount
  refine ⟨d, K, L₀, hd, hK, hL₀, ?_⟩
  intro lo hi hlo hlohi hlen N M a hN hM ha hmod
  obtain ⟨r, hr, hcop⟩ := isUnit_exists_coprime_int_rep hM a ha
  simpa only [hr] using h lo hi hlo hlohi hlen N M r hN hM hcop hmod

end Ostmann.Arithmetic.PrimeProgression

end OAI
