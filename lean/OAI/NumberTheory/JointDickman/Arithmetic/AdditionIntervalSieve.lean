import OAI.NumberTheory.JointDickman.Arithmetic.AdditionSieveMajorant

namespace OAI

/-! # Uniform interval bounds for an addition product -/

namespace JointDickman

open Finset

/-- The quarter-product probability on an interval is controlled by its
relative length and the explicit sieve remainder, uniformly in the upper
prime cutoff. -/
theorem addition_product_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P Z u v : ℕ) (Q : Finset ℕ) (X : ℝ),
      u ≤ v → 2 ≤ Z → 0 < X →
      (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q, P < p) →
      (Nat.primesLE Z).filter (fun p => P < p) ⊆ Q →
      (∀ n ∈ Ico u v, X ≤ (n : ℝ)) →
      (∑ n ∈ Ico u v, primeProductMass Q (1 / 4) n) ≤
        K * (((v : ℝ) - u) / (X * Real.log Z)) + 2 * (Z + 1 : ℝ) * Z / X := by
  obtain ⟨C, hC, hsieve⟩ := single_form_interval_sieve hFord hM
  obtain ⟨D, hD, hdensity⟩ := additionSieve_density_log_bound hM
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro P Z u v Q X huv hZ hX hQ hrough hprefix hlow
  have hZ1 : (1 : ℝ) < Z := by exact_mod_cast (by omega : 1 < Z)
  have hlog : 0 < Real.log Z := Real.log_pos hZ1
  have hq := primeNormalizer_bounds Q hQ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hlen : 0 ≤ (v : ℝ) - u := sub_nonneg.mpr (by exact_mod_cast huv)
  have hw := hsieve (Nat.primesLE Z) (additionSieveTheta P) u v Z huv hZ
    (fun p hp => ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1,
      (Nat.mem_primesLE.mp hp).2.two_le⟩)
    (fun p hp => additionSieveTheta_bounds P (Nat.mem_primesLE.mp hp).2.two_le)
  change (∑ n ∈ Ico u v, additionSieveWeight P Z n) ≤
    C * ((v : ℝ) - u) * additionSieveDensity P Z + 2 * (Z + 1 : ℝ) * Z at hw
  have hqD : primeNormalizer Q (1 / 4) * additionSieveDensity P Z ≤ D / Real.log Z := by
    apply (le_div_iff₀ hlog).mpr
    calc
      _ ≤ primeNormalizer ((Nat.primesLE Z).filter (fun p => P < p)) (1 / 4) *
          additionSieveDensity P Z * Real.log Z := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (quarterNormalizer_le_prefix hQ hprefix)
            (additionSieveDensity_nonneg P Z)) hlog.le
      _ ≤ D := hdensity P Z hZ
  have hsum : (∑ n ∈ Ico u v, primeProductMass Q (1 / 4) n) ≤
      (primeNormalizer Q (1 / 4) / X) * ∑ n ∈ Ico u v, additionSieveWeight P Z n := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    apply (quarter_primeProductMass_le_sieve P Z n hQ hrough).trans
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hq.1 hX (hlow n hn)) (additionSieveWeight_nonneg P Z n)
  calc
    _ ≤ _ := hsum
    _ ≤ (primeNormalizer Q (1 / 4) / X) *
        (C * ((v : ℝ) - u) * additionSieveDensity P Z + 2 * (Z + 1 : ℝ) * Z) :=
      mul_le_mul_of_nonneg_left hw (div_nonneg hq.1 hX.le)
    _ = (C * ((v : ℝ) - u) * (primeNormalizer Q (1 / 4) * additionSieveDensity P Z) +
        primeNormalizer Q (1 / 4) * (2 * (Z + 1 : ℝ) * Z)) / X := by ring
    _ ≤ (C * ((v : ℝ) - u) * (D / Real.log Z) + 2 * (Z + 1 : ℝ) * Z) / X := by
      apply div_le_div_of_nonneg_right _ hX.le
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hqD (mul_nonneg hC.le hlen)
      · exact mul_le_of_le_one_left (by positivity) hq.2
    _ = _ := by ring

end JointDickman

end OAI
