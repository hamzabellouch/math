import OAI.Analysis.Pureness.Divisibility.SmallHereditaryRank

namespace OAI
namespace CuntzPureness
open scoped ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_small_rank_trace_transfer (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (p : A) (hp : 0 ≤ p) (N : ℕ) (hN : 1 ≤ N) :
    ∃ h c : A, 0 ≤ h ∧ h ≠ 0 ∧ 0 ≤ c ∧ c ∈ hereditaryCarrier h ∧
      (∀ τ : TracialState A, τ.functional c = τ.functional p) ∧
      (∀ τ : TracialState A, normalizedRootRank τ c ≤ normalizedRootRank τ h ∧
        normalizedRootRank τ h ≤ 1 / (N : ℝ≥0∞)) := by
  obtain ⟨h, hh, hh0, hsmall⟩ := small_hereditary_rank hsimple hinf hT N hN
  obtain ⟨c, hc, hcm, hτ, hr⟩ := exists_rank_dominated_trace_transfer hsimple h p hh hh0 hp
  exact ⟨h, c, hh, hh0, hc, hcm, hτ, fun τ => ⟨hr τ, hsmall τ⟩⟩

theorem exists_arbitrarily_small_rank_trace_transfer (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (p : A) (hp : 0 ≤ p) (η : ℝ) (hη : 0 < η) :
    ∃ c : A, 0 ≤ c ∧ (∀ τ : TracialState A, τ.functional c = τ.functional p) ∧
      (∀ τ : TracialState A, normalizedRootRank τ c < ENNReal.ofReal η) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  have hNp : (0 : ℝ) < N := (one_div_pos.mpr hη).trans hN
  have hNnat : 1 ≤ N := by exact_mod_cast hNp
  have hinv : 1 / (N : ℝ) < η := by
    apply (div_lt_iff₀ hNp).mpr
    have := (div_lt_iff₀ hη).mp hN
    simpa only [mul_comm] using this
  have hinvE : (1 : ℝ≥0∞) / (N : ℝ≥0∞) < ENNReal.ofReal η := by
    have ht := (ENNReal.ofReal_lt_ofReal_iff hη).mpr hinv
    simpa only [ENNReal.ofReal_div_of_pos hNp, ENNReal.ofReal_one, ENNReal.ofReal_natCast] using ht
  obtain ⟨h, c, hh, hh0, hc, hcm, hτ, hr⟩ :=
    exists_small_rank_trace_transfer hsimple hinf hT p hp N hNnat
  exact ⟨c, hc, hτ, fun τ => ((hr τ).1.trans (hr τ).2).trans_lt hinvE⟩
end CuntzPureness

end OAI
