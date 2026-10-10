import OAI.Analysis.Pureness.Completion.CompletedSandwichBudget

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ENNReal NNReal

theorem finite_ennreal_rank_sandwich (n : ℕ) (hn : 1 ≤ n)
    (r b : ℝ≥0∞) (m s E : ℝ) (hm : 0 < m) (hE0 : 0 ≤ E)
    (hslo : 1 / ((n : ℝ)+1) < s) (hshi : s < 1 / (n : ℝ))
    (hE : E < (s - 1 / ((n : ℝ)+1))*m)
    (hmr : ENNReal.ofReal m ≤ r) (hb : b ≤ ENNReal.ofReal s * r)
    (hupper : ENNReal.ofReal s * r ≤ b + ENNReal.ofReal E) (hr : r ≠ ⊤) :
    (n : ℝ≥0∞)*b < r ∧ r < ((n+1 : ℕ) : ℝ≥0∞)*b := by
  have hs : 0 < s := (by positivity : (0 : ℝ) < 1/((n : ℝ)+1)).trans hslo
  have hsr : ENNReal.ofReal s * r ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr
  have hbf : b ≠ ⊤ := ne_of_lt (hb.trans_lt (lt_top_iff_ne_top.mpr hsr))
  have hsum : b + ENNReal.ofReal E ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hbf, ENNReal.ofReal_ne_top⟩
  have hl := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hr).mpr hmr
  have hb' := (ENNReal.toReal_le_toReal hbf hsr).mpr hb
  have hu := (ENNReal.toReal_le_toReal hsr hsum).mpr hupper
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.le, ENNReal.toReal_ofReal hs.le,
    ENNReal.toReal_add hbf ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hE0] at hl hb' hu
  obtain ⟨h1,h2⟩ := finite_rank_sandwich n hn r.toReal b.toReal m s E hm hl hslo hshi hE hb' hu
  constructor
  · apply (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top (by simp) hbf) hr).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h1
  · apply (ENNReal.toReal_lt_toReal hr (ENNReal.mul_ne_top (by simp) hbf)).mp
    simpa [ENNReal.toReal_mul, ENNReal.toReal_add] using h2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_completed_strict_sandwich_ranks (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (a : CornerCompletion A) (ha : 0 ≤ a) (ha0 : a ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ b : CornerCompletion A, 0 ≤ b ∧ b ≠ 0 ∧ ∀ τ : TracialState A,
      (completedRootRank τ a = ⊤ ↔ completedRootRank τ b = ⊤) ∧
      (completedRootRank τ a ≠ ⊤ →
        (n : ℝ≥0∞)*completedRootRank τ b < completedRootRank τ a ∧
        completedRootRank τ a < ((n+1 : ℕ) : ℝ≥0∞)*completedRootRank τ b) := by
  obtain ⟨b,m,s,E,hb,hm,hE0,hslo,hshi,hE,hr⟩ :=
    exists_completed_source_budget hsimple hinf hT a ha ha0 n hn
  have hs : 0 < s := (by positivity : (0 : ℝ) < 1/((n : ℝ)+1)).trans hslo
  have htop (τ : TracialState A) := rank_top_iff_of_budget
    (by exact ENNReal.ofReal_ne_zero_iff.mpr hs) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (hr τ).2.1 (hr τ).2.2
  have hstrict (τ : TracialState A) (hf : completedRootRank τ a ≠ ⊤) :=
    finite_ennreal_rank_sandwich n hn (completedRootRank τ a) (completedRootRank τ b)
      m s E hm hE0 hslo hshi hE (hr τ).1 (hr τ).2.1 (hr τ).2.2 hf
  have hb0 : b ≠ 0 := by
    intro hz
    obtain ⟨τ⟩ := hT
    by_cases hf : completedRootRank τ a = ⊤
    · have hh := (htop τ).mp hf
      simp [hz] at hh
    · have hh := (hstrict τ hf).2
      simp [hz] at hh
  exact ⟨b,hb,hb0,fun τ => ⟨htop τ,hstrict τ⟩⟩
end CuntzPureness

end

end OAI
