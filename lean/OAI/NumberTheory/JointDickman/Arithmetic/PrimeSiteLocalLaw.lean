import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSiteBridge
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductResidueLaw

namespace OAI

/-! # Local product laws for the actual Boolean prime sites -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem primeSite_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ x : auxiliaryPrimes B → Bool,
          if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
              (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
            bernoulliSiteMass (fun p : auxiliaryPrimes B => z / p.val) x else 0) -
          (∫ s in a..b, scaledRoughDensity c z H B s) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨c, hc, hcpos, H, C, hC, hbound⟩ := primeProduct_residue_local_interval_law hSD hSW hM hz
  refine ⟨c, hc, hcpos, H, C, hC, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hboundB hB
  intro a b ha hab hb q _ hq r
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let K := (Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊).filter
    (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q))
  have hevent (x : auxiliaryPrimes B → Bool) :
      (Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
        (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r) ↔
      retainedPrimeProduct (auxiliaryPrimes B) x ∈ K := by
    have hnpos : (0 : ℝ) < retainedPrimeProduct (auxiliaryPrimes B) x := by
      exact_mod_cast retainedPrimeProduct_pos (auxiliaryPrimes B) (auxiliaryPrimes_prime B) x
    simp only [K, mem_filter, mem_Ioc, Set.mem_Ioc]
    rw [Nat.floor_lt (by positivity : 0 ≤ Real.exp (B * a)), Nat.le_floor_iff (by positivity : 0 ≤ Real.exp (B * b))]
    rw [lt_div_iff₀ hB0, div_le_iff₀ hB0]
    rw [Real.lt_log_iff_exp_lt hnpos, Real.log_le_iff_le_exp hnpos]
    ring_nf
  have hsum : (∑ x : auxiliaryPrimes B → Bool,
      if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
        bernoulliSiteMass (fun p : auxiliaryPrimes B => z / p.val) x else 0) =
        ∑ n ∈ K, primeProductMass (auxiliaryPrimes B) z n := by
    simp_rw [hevent]
    exact primeSiteMass_event (auxiliaryPrimes B) z K
  rw [hsum]
  exact hboundB a b ha hab hb q hq r


open Classical in
theorem quarterPrimeSite_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 4) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ x : auxiliaryPrimes B → Bool,
          if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
              (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
            quarterPrimeMass (auxiliaryPrimes B) x else 0) -
          (∫ s in a..b, scaledRoughDensity c (1 / 4) H B s) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  have h := primeSite_local_law hSD hSW hM
    (Or.inl rfl : (1 / 4 : ℝ) = 1 / 4 ∨ (1 / 4 : ℝ) = 1 / 2)
  simpa only [quarterPrimeMass_eq] using h

end JointDickman

end OAI
