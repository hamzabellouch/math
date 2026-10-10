import OAI.Analysis.Pureness.Divisibility.SmallTraceTransfer
import OAI.Analysis.Pureness.Cuntz.ActualSpectralCuts
import OAI.Analysis.Pureness.Divisibility.SourceRankLimit

namespace OAI
namespace CuntzPureness
open scoped ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_integer_cut_rank_approximation (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (p : A) (hp : 0 ≤ p) (η : ℝ) (hη : 0 < η) :
    ∃ c : A, ∃ l : ℕ, 0 ≤ c ∧ ‖c‖ < l ∧
      (∀ j, 0 ≤ positiveIntegerCut c j) ∧
      (∀ τ : TracialState A,
        0 ≤ (τ.functional p).re - ∑ j ∈ Finset.range l, (normalizedRootRank τ (positiveIntegerCut c j)).toReal ∧
        (τ.functional p).re - ∑ j ∈ Finset.range l, (normalizedRootRank τ (positiveIntegerCut c j)).toReal < η) := by
  obtain ⟨c, hc, hτ, hr⟩ := exists_arbitrarily_small_rank_trace_transfer hsimple hinf hT p hp η hη
  obtain ⟨l, hl⟩ := exists_nat_gt ‖c‖
  refine ⟨c, l, hc, hl, positiveIntegerCut_nonneg c, ?_⟩
  intro τ
  have hfinite : normalizedRootRank τ c ≠ ∞ :=
    ne_of_lt ((normalizedRootRank_le_one τ c hc).trans_lt ENNReal.one_lt_top)
  have hηr : (normalizedRootRank τ c).toReal < η := by
    have h := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr (hr τ)
    simpa only [ENNReal.toReal_ofReal hη.le] using h
  have hb := actual_spectral_integer_approximation τ c hc l hl.le
  rw [hτ τ] at hb
  exact ⟨hb.1, hb.2.trans_lt hηr⟩
end CuntzPureness

end OAI
