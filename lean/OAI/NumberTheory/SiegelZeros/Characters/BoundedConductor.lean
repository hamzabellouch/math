import OAI.NumberTheory.SiegelZeros.Estimates.ContrarySequence
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalGap

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W02

theorem bounded_conductor_zero_gap (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≤ Q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, β < 1 → χ.LFunction (β : ℂ) = 0 →
        c ≤ (1 - β) * Real.log (q : ℝ) := by
  induction Q with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro q hzero hq hQ
      omega
  | succ Q ih =>
      obtain ⟨c, hc, hbound⟩ := ih
      by_cases hQ : 3 ≤ Q + 1
      · have : NeZero (Q + 1) := ⟨by omega⟩
        obtain ⟨ε, hε, hgap⟩ := fixed_level_real_zero_gap (Q + 1)
        have hlog : 0 < Real.log ((Q + 1 : ℕ) : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < Q + 1 by omega))
        refine ⟨min c (ε * Real.log ((Q + 1 : ℕ) : ℝ)),
          lt_min_iff.mpr ⟨hc, mul_pos hε hlog⟩, ?_⟩
        intro q hzero hq hqQ χ hχ β hβ hz
        by_cases hle : q ≤ Q
        · exact (min_le_left _ _).trans (hbound q hq hle χ hχ β hβ hz)
        · have heq : q = Q + 1 := by omega
          subst q
          exact (min_le_right _ _).trans
            (mul_le_mul_of_nonneg_right (hgap χ hχ β hβ hz) hlog.le)
      · refine ⟨c, hc, ?_⟩
        intro q hzero hq hqQ
        omega

end WeightedTorusJets.W02


end SiegelZeros

end OAI
