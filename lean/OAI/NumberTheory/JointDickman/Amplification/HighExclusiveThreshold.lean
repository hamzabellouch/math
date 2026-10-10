import OAI.NumberTheory.JointDickman.Amplification.HighExclusiveLocalLaw

namespace OAI

/-! # High-exclusive local law for fixed smoothing thresholds -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The retained exclusive cell is approximated by a residue-independent
integral, uniformly even for a partial cell at the high cutoff. -/
theorem highExclusiveLogCell_threshold_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧ 0 < v 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ θ : ℝ, (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ θ →
        ∀ lower upper : D → ℝ,
        (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
        (∀ d, upper d ≤ 16 / 5) → ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
        |highExclusiveCell (quarterPrimeMass (auxiliaryPrimes B))
            (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper))
            (lowPrimeLog (auxiliaryPrimes B) B θ) c (d, r) -
          clippedIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
            θ (lower d) (upper d)
            (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨v, hv, hvpos, H, C, hC, hbound⟩ := quarterPrimeSite_local_law hSD hSW hM
  refine ⟨v, hv, hvpos, H, C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro D _ q _ hq θ hθ lower upper hdisjoint hupper c d r
  have hqP := auxiliary_modulus_le_cutoff hB hq
  have hcut : ∀ p ∈ auxiliaryPrimes B, q < p := by
    intro p hp
    have hP : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hp).2
    exact hqP.trans_lt hP
  let u := ZMod.unitOfCoprime (retainedPrimeProduct (auxiliaryPrimes B) c)
    (retainedPrimeProduct_coprime (auxiliaryPrimes B) (auxiliaryPrimes_prime B) (NeZero.ne q) hcut c)
  rw [highExclusiveLogCell_eq (auxiliaryPrimes B) (auxiliaryPrimes_prime B) B q lower upper
    hdisjoint _ c u r rfl d]
  let t := Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / (B : ℝ)
  have ht : 0 ≤ t := div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  let a := max θ (lower d - t)
  let b := upper d - t
  by_cases hab : a ≤ b
  · have ha : (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a := hθ.trans (le_max_left _ _)
    have hb : b ≤ 16 / 5 := by dsimp [b]; linarith [hupper d]
    have hh := hboundB a b ha hab hb q hq (u⁻¹ * r)
    simpa only [clippedIntervalIntegral, t, a, b, ite_eq_left hab] using hh
  · have hempty : ∀ e : auxiliaryPrimes B → Bool,
        ¬(Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
      rintro e ⟨he, _⟩
      exact hab (le_trans he.1.le he.2)
    have hsum : (∑ e : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)
        then quarterPrimeMass (auxiliaryPrimes B) e else 0) = 0 := by
      apply sum_eq_zero
      intro e _
      exact ite_eq_right (hempty e)
    change |(∑ e : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)
        then quarterPrimeMass (auxiliaryPrimes B) e else 0) - _| ≤ _
    have hclip : clippedIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
        θ (lower d) (upper d)
        (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) = 0 := by
      change (if a ≤ b then _ else 0) = 0
      exact ite_eq_right hab
    rw [hsum, hclip]
    simp only [zero_div, sub_self, abs_zero]
    positivity


end JointDickman

end OAI
