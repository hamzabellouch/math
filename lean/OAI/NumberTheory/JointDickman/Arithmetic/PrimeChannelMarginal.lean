import OAI.NumberTheory.JointDickman.Arithmetic.PrimeCommonCell
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeMarginalComparison

namespace OAI

/-! # Marginal bounds for the actual partial logarithmic channel -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem primeLogCell_eq {D : Type*} [DecidableEq D]
    (Q : Finset ℕ) (B q : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (w : (Q → Bool) → ℝ) (d : D) (r : (ZMod q)ˣ) :
    optionCellMass w (fun x => logResidueCell B q lower upper (retainedPrimeProduct Q x)) (d, r) =
      ∑ x : Q → Bool, if Real.log (retainedPrimeProduct Q x) / B ∈ Set.Ioc (lower d) (upper d) ∧
          (retainedPrimeProduct Q x : ZMod q) = r then w x else 0 := by
  unfold optionCellMass
  apply sum_congr rfl
  intro x _
  simp only [logResidueCell_eq_some B q lower upper hdisjoint]

open Classical in
/-- The independent common/exclusive marginal is bounded by the half-prime
local law plus the proved finite two-split comparison error. -/
theorem primeChannelMarginal_upper
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ lower upper : D → ℝ,
      (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
      (∀ d, 1 / 4 ≤ lower d) → (∀ d, lower d ≤ upper d) → (∀ d, upper d ≤ 16 / 5) →
      ∀ d : D, ∀ r : (ZMod q)ˣ,
      independentCellMarginal (quarterPrimeMass (auxiliaryPrimes B))
        (quarterPrimeMass (auxiliaryPrimes B))
        (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper)) (d, r) ≤
        M * (upper d - lower d) / q.totient + C * (B : ℝ) ^ (-(80 : ℝ)) +
          9 / (8 * (auxiliaryCutoff B : ℝ)) := by
  obtain ⟨M, C, hM0, hC, hbound⟩ := primeSite_interval_upper hSD hSW hM hMP
    (Or.inr rfl : (1 / 2 : ℝ) = 1 / 4 ∨ (1 / 2 : ℝ) = 1 / 2)
  refine ⟨M, C, hM0, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro D _ q _ hq lower upper hdisjoint hlower horder hupper d r
  have hcut : ∀ p ∈ auxiliaryPrimes B, auxiliaryCutoff B < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have hN : auxiliaryCutoff B ≠ 0 := pow_ne_zero _ (by omega)
  have he := independentPrimeMarginal_fair_error (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    hN hcut (logResidueCell B q lower upper) (d, r)
  rw [primeLogCell_eq _ B q lower upper hdisjoint] at he
  have hw : (fun p : auxiliaryPrimes B => 1 / (2 * (p.val : ℝ))) =
      (fun p : auxiliaryPrimes B => (1 / 2 : ℝ) / p.val) := by
    funext p
    ring
  rw [hw] at he
  have hb := hboundB (lower d) (upper d) (hlower d) (horder d) (hupper d) q hq r
  have he' := (abs_le.mp he).2
  linarith

end JointDickman

end OAI
