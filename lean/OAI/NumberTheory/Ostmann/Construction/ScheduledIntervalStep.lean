import OAI.NumberTheory.Ostmann.Arithmetic.IntervalArithmeticStep
import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyHistory

namespace OAI

/-! # The actual finite history family satisfies the interval arithmetic step -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentPrimeGuardedAmplitude_scheduled_step {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (hpivot : ∀ k, role (pivot k).1 = .pivot k)
    (n : ℕ) (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i q, q ∈ P → ‖κ i q‖ ≤ 1)
    (hQP : ∀ i, Q i ⊆ P) (hQ : ∀ i, (∑ q ∈ Q i, (q : ℝ)⁻¹) ≠ 0)
    (lo hi : I → ℕ) (cellLo cellHi : (Σ i, Fin (size i)) → ℕ)
    (hcell : ∀ i q, q ∈ Q i → cellLo i ≤ q ∧ q ≤ cellHi i)
    (V : ℕ → ℕ) (hV : Monotone V) (pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (center : ∀ p : ℕ, ZMod p) (K : ℕ)
    (hpLo : 0 < lo p) (hpHi : hi p ≤ pivotBound n)
    (hcellLo : lo p ≤ ∏ k : Fin (size p), cellLo ⟨p, k⟩)
    (hcellHi : (∏ k : Fin (size p), cellHi ⟨p, k⟩) ≤ hi p)
    (hzero : ∀ x, fullAtomTransferWeight role V pivotBound
      (atomIntervalRanges role lo hi) leaf 0 x (0 : ℤ) = 0)
    (hK : (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
      cellHi (copyScheduleOrigin n h.val)) ≤ K)
    (hgap : 2 * pivotBound n * V n <
      ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n, cellLo (copyScheduleOrigin n h.val))
    (hscale : 2 * V n * K ≤ V (n + 1) * lo p) (hprime : ∀ q ∈ P, V (n + 1) < q)
    (loss : ℝ) (hcost : (((size p).factorial : ℝ) *
      ∏ i : Fin (size p), (∑ q ∈ Q ⟨p, i⟩, (q : ℝ)⁻¹)⁻¹) ≤ Real.exp loss) :
    Real.exp (-loss) *
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
        V pivotBound (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V n) center‖ ^ 2 ≤
      (∑ u, (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
        ∑ M ∈ Finset.Icc (lo p) (hi p), (constituentPivotDiagonal role size χ κ pivot n P hP Q
          V pivotBound (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V n) center u M).re) +
      ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
        V pivotBound (atomIntervalRanges role lo hi) leaf (scheduledFrequencyHistory V (n + 1)) center‖ := by
  have ht := constituentPrimeGuardedAmplitude_interval_step role size χ κ pivot hpivot n p hp hu
    P hP Q hκ hQP hQ lo hi cellLo cellHi hcell V pivotBound leaf
    (scheduledFrequencyHistory V n) center K (V (n + 1)) hpLo hpHi hcellLo hcellHi
    (scheduledFrequencyHistory_root_bound V n) hzero (by
      intro d s hs q hq
      exact (scheduledFrequencyHistory_all_bound V hV n d s hs).trans_lt
        ((hV (Nat.le_succ n)).trans_lt (hprime q hq)))
    hK hgap hscale hprime loss hcost
  rw [← scheduledFrequencyHistory_succ] at ht
  exact ht

end Ostmann

end OAI
