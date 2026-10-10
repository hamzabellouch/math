import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSourceFlagReplacement
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
attribute [local instance] Classical.propDecidable

theorem positiveSourceValue_abs_le (S : PrimeSource) (B : ℝ)
    (hcap : ∀ v : S.Sample, S.law.mass v ≠ 0 → ((v:ℕ):ℝ) ≤ B)
    {z : ℤ} (hz : PositiveSourceValue S z) : |(z:ℝ)| ≤ B := by
  obtain ⟨v,rfl,hv⟩ := hz
  simpa only [Int.cast_natCast,abs_of_nonneg (show (0:ℝ) ≤ (v.val:ℝ) from Nat.cast_nonneg _)] using hcap v hv

theorem dummyMass_non_giant_abs_le {ι ρ η : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq η]
    (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (e : SourceIndex ρ (Block p) ≃ η) (q : Block p) (B : ℝ)
    (hroots : ∀ i, ∀ v : (roots i).Sample,
      (roots i).law.mass v ≠ 0 → ((v:ℕ):ℝ) ≤ B)
    (hsources : ∀ i, ∀ v : (sources i).Sample,
      (sources i).law.mass v ≠ 0 → ((v:ℕ):ℝ) ≤ B)
    (j : η) (hj : ∀ t, j ≠ e (.inl t)) (z : ℤ)
    (hz : dummyMass giants roots sources origin p e q j z ≠ 0) : |(z:ℝ)| ≤ B := by
  by_cases hq : j = e (.inr (.inr q))
  · subst j
    simp only [dummyMass,Function.update_self] at hz
    obtain ⟨v,hv,hw⟩ := integerWeight_ne_zero _ _ hz
    exact positiveSourceValue_abs_le _ B (hsources _)
      (hv ▸ positiveSourceValue_of_sourceWeight sources origin (blockAnchor p q).val v hw)
  · simp only [dummyMass,Function.update_of_ne hq] at hz
    rcases hi : e.symm j with t | i | r
    · exact (hj t (by rw [← hi,e.apply_symm_apply])).elim
    · rw [hi] at hz
      exact positiveSourceValue_abs_le _ B (hroots i)
        (positiveSourceValue_of_integerWeight (roots i) hz)
    · rw [hi] at hz
      exact positiveSourceValue_abs_le _ B (hsources _)
        (positiveSourceValue_of_block_integerWeight sources origin p r hz (blockAnchor p r))

end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
