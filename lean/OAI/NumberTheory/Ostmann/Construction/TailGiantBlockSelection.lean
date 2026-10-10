import OAI.NumberTheory.Ostmann.Construction.CompleteTailGiantMean
import OAI.NumberTheory.Ostmann.Construction.GiantMeanGap

namespace OAI

/-! # A full smooth giant selected from a favorable logarithmic prime block -/

namespace Ostmann
open scoped Classical BigOperators

/-- The favorable set affects only the test. The chosen prior contains every
prime of the complete selected cell, and its lower mean is absolute. -/
theorem tail_giant_of_favorable_block {A B : Set ℕ}
    (hA : A.Infinite) (hB : B.Infinite) (N : ℕ)
    (F E D : Finset ℕ) (ν : ℕ → ℝ) (lo h γ c B₀ C : ℝ)
    (hM : MertensEstimate C) (hlo : 5 ≤ lo) (hh : 0 < h)
    (hγ : 0 < γ) (hc : 0 < c) (hB0 : 0 ≤ B₀)
    (hwidth : 8 + Real.log 2 + 2 * C ≤ h)
    (hupper : lo + h ≤ 2 * (lo - 4))
    (hdisjoint : ∀ p ∈ smoothGiantPrimeRange (lo + h + 2),
      Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hF : ∀ p ∈ F, p.Prime ∧ lo ≤ Real.log p ∧ Real.log p ≤ lo + h)
    (hFbal : ∀ p ∈ F, ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3)
    (hFγ : ∀ p (hp : p ∈ F), let _ : Fact p.Prime := ⟨(hF p hp).1⟩;
      γ ≤ (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖)
    (hE : ∀ p ∈ smoothGiantPrimeRange (lo + h + 2), ∀ a ∈ E, a ∈ A ∧ N + p < a)
    (hbudget : (∑ p ∈ smoothGiantPrimeRange (lo + h + 2),
      Real.log (p : ℝ) * tailCollisionDefect A N p E D
        (fun _ => (E.card : ℝ)⁻¹) ν) ≤ B₀)
    (hFmass : c * h ≤ ∑ p ∈ F, Real.log (p : ℝ) / p)
    (hsmall : B₀ ≤ γ ^ 2 * c ^ 2 * h / 512) :
    ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ lo + h + 2 ∧
      0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
      γ * c / 32 < ∑ p : smoothGiantPrimeRange G,
        smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p *
          tailGiantEndpointMean A N F E p := by
  let P := smoothGiantPrimeRange (lo + h + 2)
  have hFP : F ⊆ P := by
    intro p hp
    obtain ⟨hpp, _, hpu⟩ := hF p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hpp.pos, ?_⟩, hpp⟩
    have hlog : Real.log (p : ℝ) ≤ lo + h + 2 + 1 := by linarith
    have he : (p : ℝ) ≤ Real.exp (lo + h + 2 + 1) :=
      (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hpp.pos)).mp hlog
    exact_mod_cast he.trans (Nat.le_ceil _)
  obtain ⟨G, hGC, hmass, hmean⟩ := tail_giant_positive_cell hA hB N P
    (smoothGiantPrimeRange_prime _) hdisjoint F E D hFP ν lo (lo + h) γ (γ * c / 32) B₀
    (by linarith) (logBlockCenters_full_cells lo (lo + h))
    (fun p hp => (hF p hp).2) hFbal hFγ hE hbudget
    (logBlock_giant_mean_gap hM P F (smoothGiantPrimeRange_prime _) lo h γ c B₀
      hlo hh hγ hc hB0 hwidth hupper (fun p hp => (hF p hp).2.2) hFmass hsmall)
  obtain ⟨hGlo, hGhi⟩ := logBlockCenters_bounds lo (lo + h) hGC
  exact ⟨G, hGlo, hGhi, hmass, hmean⟩

end Ostmann

end OAI
