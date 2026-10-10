import OAI.NumberTheory.Ostmann.Construction.RetainedKernelPrimeBound
import OAI.NumberTheory.Ostmann.Construction.InfiniteSplitMass

namespace OAI

/-! # Quantitative split-prime mass for a retained signed squarefree kernel -/

namespace Ostmann

open scoped BigOperators Classical

/-- Every term of the lower bound is derived: the main pole, the actual
character zero sum, the prime tail, and the excluded-divisor weight. -/
theorem retained_split_prime_mass (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A K C : ℝ, 0 < A ∧ 0 < K ∧ 0 < C ∧
      ∀ d : ℤ, Squarefree d.natAbs → 2 < d.natAbs →
        ∃ (χ : PrimitiveRealCharacter) (N : ℕ),
          1 < N ∧ N ∣ χ.modulus ∧ χ.modulus ≤ 8 * N ∧
          (d.natAbs = N ∨ d.natAbs = 2 * N) ∧
          χ.modulus ≤ 4 * d.natAbs ∧ d.natAbs ≤ 2 * χ.modulus ∧
          ∀ (Q₀ Q D Y : ℕ) (R s : ℝ),
            2 ≤ Q₀ → 4 * d.natAbs ≤ Q₀ → 0 < Q → 0 < D → 0 < Y →
            d.natAbs ∣ D → 0 ≤ R →
            2 * (A + H.errorConstant) ≤ Real.log (4 * (Q₀ : ℝ)) →
            1 < s → s ≤ 2 → s ≤ 1 + 1 / Real.log (4 * (Q₀ : ℝ)) →
            (∀ e : PrimitiveRealZero, selectedPageZero P Q₀ = some e →
              samePrimitiveRealCharacter e χ → (e.modulus : ℝ) ≤ R) →
            (1 / (s - 1) - C -
                (2 * zeroComparisonConstant P * Real.log (4 * (Q₀ : ℝ)) +
                  K * R ^ ε + H.errorConstant + A + 2)) / 2 -
              (Q : ℝ) ^ (-(s - 1) / 2) * (2 / (s - 1) + C) -
              (Y + Real.log D / Y) ≤
              ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
                Real.log p / (p : ℝ) := by
  obtain ⟨A, K, hA, hK, hkernel⟩ := retained_signed_kernel_prime_lower P H hSiegel ε hε
  obtain ⟨Cu, hCu, hmass⟩ := exists_unsignedPrimeMass_error
  obtain ⟨Ct, hCt, htail⟩ := exists_unsignedPrimeTail_bound
  let C := Cu + Ct
  have hCuC : Cu ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨A, K, C, hA, hK, by dsimp [C]; positivity, ?_⟩
  intro d hsf hd
  obtain ⟨χ, N, hN, hNq, hqN, hdN, hqd, hdq, hk⟩ := hkernel d hsf hd
  refine ⟨χ, N, hN, hNq, hqN, hdN, hqd, hdq, ?_⟩
  intro Q₀ Q D Y R s hQ₀ hdQ₀ hQ hD hY hdD hR hsize hs hs2 hss hretain
  obtain ⟨hj, hJ⟩ := hk Q₀ R s hQ₀ hdQ₀ hR hsize hs hss hretain
  obtain ⟨hu, hU⟩ := hmass s hs hs2
  obtain ⟨ht, hT⟩ := htail Q s hQ hs hs2
  have hUl : 1 / (s - 1) - C ≤ ∑' n, unsignedPrimeTerm s n := by
    have hh := (abs_le.mp hU).1
    linarith
  have hTl : (∑' n, unsignedPrimeTail Q s n) ≤
      (Q : ℝ) ^ (-(s - 1) / 2) * (2 / (s - 1) + C) :=
    hT.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg Q) _))
  have hb : -(2 * zeroComparisonConstant P * Real.log (4 * (Q₀ : ℝ)) +
      K * R ^ ε + H.errorConstant + A + 2) ≤ ∑' n, jacobiPrimeTerm d s n := by
    linarith
  have hsplit := retained_split_mass_from_series d D Q Y s _ _ _ hdD hD hY hs.le hu hj ht hUl hb hTl
  apply hsplit.trans
  apply Finset.sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) hp0
    (Real.self_le_rpow_of_one_le hp1 hs.le)

end Ostmann

end OAI
