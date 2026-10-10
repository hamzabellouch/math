import OAI.NumberTheory.JointDickman.Amplification.ProductLogCells

namespace OAI

/-! # Local laws for the high-exclusive part of the actual prime channel -/

namespace JointDickman

open Filter Finset
open scoped Topology

def lowPrimeLog (Q : Finset ℕ) (B : ℕ) (θ : ℝ) (x : Q → Bool) : Prop :=
  Real.log (retainedPrimeProduct Q x) / B ≤ θ

open Classical in
noncomputable def clippedIntervalIntegral (f : ℝ → ℝ) (θ a b t : ℝ) : ℝ :=
  if max θ (a - t) ≤ b - t then ∫ s in max θ (a - t)..b - t, f s else 0

open Classical in
theorem highExclusiveLogCell_eq {D : Type*} [DecidableEq D]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (B q : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (θ : ℝ) (c : Q → Bool) (u r : (ZMod q)ˣ)
    (hu : (retainedPrimeProduct Q c : ZMod q) = u) (d : D) :
    highExclusiveCell (quarterPrimeMass Q)
      (primeProductCell Q (logResidueCell B q lower upper)) (lowPrimeLog Q B θ) c (d, r) =
      ∑ e : Q → Bool,
        if Real.log (retainedPrimeProduct Q e) / B ∈
            Set.Ioc (max θ (lower d - Real.log (retainedPrimeProduct Q c) / B))
              (upper d - Real.log (retainedPrimeProduct Q c) / B) ∧
          (retainedPrimeProduct Q e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ) then
          quarterPrimeMass Q e else 0 := by
  rw [highExclusiveCell_eq_sum]
  apply sum_congr rfl
  intro e _
  have hiff : (¬lowPrimeLog Q B θ e ∧
      primeProductCell Q (logResidueCell B q lower upper) c e = some (d, r)) ↔
      (Real.log (retainedPrimeProduct Q e) / B ∈
        Set.Ioc (max θ (lower d - Real.log (retainedPrimeProduct Q c) / B))
          (upper d - Real.log (retainedPrimeProduct Q c) / B) ∧
        (retainedPrimeProduct Q e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
    dsimp only [lowPrimeLog, primeProductCell]
    rw [not_le, logResidueCell_eq_some B q lower upper hdisjoint]
    exact high_product_cell_iff (retainedPrimeProduct_pos Q hQ c)
      (retainedPrimeProduct_pos Q hQ e) u r hu (lower d) (upper d) θ
  simp only [hiff]

open Classical in
/-- The retained exclusive cell is approximated by a residue-independent
integral, uniformly even for a partial cell at the high cutoff. -/
theorem highExclusiveLogCell_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧ 0 < v 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ lower upper : D → ℝ,
        (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
        (∀ d, upper d ≤ 16 / 5) → ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
        |highExclusiveCell (quarterPrimeMass (auxiliaryPrimes B))
            (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper))
            (lowPrimeLog (auxiliaryPrimes B) B ((B : ℝ) ^ (-(1 / 10 : ℝ)))) c (d, r) -
          clippedIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
            ((B : ℝ) ^ (-(1 / 10 : ℝ))) (lower d) (upper d)
            (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨v, hv, hvpos, H, C, hC, hbound⟩ := quarterPrimeSite_local_law hSD hSW hM
  refine ⟨v, hv, hvpos, H, C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro D _ q _ hq lower upper hdisjoint hupper c d r
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
  let a := max ((B : ℝ) ^ (-(1 / 10 : ℝ))) (lower d - t)
  let b := upper d - t
  by_cases hab : a ≤ b
  · have ha : (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a := le_max_left _ _
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
        ((B : ℝ) ^ (-(1 / 10 : ℝ))) (lower d) (upper d)
        (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) = 0 := by
      change (if a ≤ b then _ else 0) = 0
      exact ite_eq_right hab
    rw [hsum, hclip]
    simp only [zero_div, sub_self, abs_zero]
    positivity

end JointDickman

end OAI
