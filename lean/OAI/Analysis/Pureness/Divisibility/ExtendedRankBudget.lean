import Mathlib.Basic.ENNReal.Inv

namespace OAI
open scoped ENNReal
namespace CuntzPureness

theorem extended_rank_budget (u b e : ℕ → ℝ≥0∞) (s E : ℝ≥0∞)
    (hlower : ∀ q, b q ≤ s * u q)
    (hupper : ∀ q, s * u q ≤ b q + e q)
    (herror : ∀ q, e q ≤ E) :
    (⨆ q, b q) ≤ s * (⨆ q, u q) ∧
      s * (⨆ q, u q) ≤ (⨆ q, b q) + E := by
  rw [ENNReal.mul_iSup]
  constructor
  · exact iSup_mono hlower
  · apply iSup_le
    intro q
    exact (hupper q).trans (add_le_add (le_iSup b q) (herror q))

theorem infinite_rank_of_budget {r b s E : ℝ≥0∞}
    (hs : s ≠ 0) (hE : E ≠ ⊤) (hr : r = ⊤) (hbudget : s * r ≤ b + E) :
    b = ⊤ := by
  subst r
  have htop : b + E = ⊤ := top_unique (by simpa [ENNReal.mul_top hs] using hbudget)
  exact (ENNReal.add_eq_top.mp htop).resolve_right hE

theorem rank_top_iff_of_budget {r b s E : ℝ≥0∞}
    (hs : s ≠ 0) (hsfinite : s ≠ ⊤) (hE : E ≠ ⊤)
    (hlower : b ≤ s * r) (hupper : s * r ≤ b + E) :
    r = ⊤ ↔ b = ⊤ := by
  constructor
  · exact fun hr => infinite_rank_of_budget hs hE hr hupper
  · intro hb
    by_contra hr
    have hfin := ENNReal.mul_ne_top hsfinite hr
    exact hfin (top_unique (by simpa [hb] using hlower))

theorem finite_compression_lt_infinite {c r : ℝ≥0∞} (k : ℕ)
    (hc : c ≤ k) (hr : r = ⊤) : c < r := by
  rw [hr]
  exact lt_of_le_of_lt hc (by simp)

theorem compression_strict_rank {c z r : ℝ≥0∞} (k : ℕ)
    (hfinite : c ≤ k) (hmono : c ≤ z)
    (hstrict : r ≠ ⊤ → z < r) : c < r := by
  by_cases hr : r = ⊤
  · exact finite_compression_lt_infinite k hfinite hr
  · exact hmono.trans_lt (hstrict hr)
end CuntzPureness

end OAI
