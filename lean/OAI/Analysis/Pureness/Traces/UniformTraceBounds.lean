import OAI.Analysis.Pureness.Traces.TracialStateTopology
import OAI.Analysis.Pureness.Traces.TracialRank
import OAI.Analysis.Pureness.Operators.CompactComparison
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma TracialState.trace_pos (τ : TracialState A) (hsimple : TopologicallySimple A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) : 0 < (τ.functional h).re := by
  have hne : τ.functional h ≠ 0 := fun heq => hh0 (τ.faithful hsimple h hh heq)
  exact (Complex.pos_iff.mp (lt_of_le_of_ne (τ.functional.map_nonneg hh) hne.symm)).1

theorem uniform_positive_trace_lower_bound (hsimple : TopologicallySimple A)
    (hT : Nonempty (TracialState A)) (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ τ : TracialState A, m ≤ (τ.functional h).re := by
  let := hT
  have hcont : Continuous (fun τ : TracialState A => (τ.functional h).re) :=
    Complex.continuous_re.comp (TracialState.continuous_eval h)
  obtain ⟨τ₀, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
  exact ⟨(τ₀.functional h).re, τ₀.trace_pos hsimple h hh hh0, fun τ => hmin (Set.mem_univ τ)⟩

theorem lowerSemicontinuous_rank (a : A) :
    LowerSemicontinuous (fun τ : TracialState A => normalizedRootRank τ a) := by
  unfold normalizedRootRank
  apply lowerSemicontinuous_iSup
  intro n
  exact (ENNReal.continuous_ofReal.comp
    (Complex.continuous_re.comp (TracialState.continuous_eval (normalizedRoot a n)))).lowerSemicontinuous

lemma isOpen_lt_rank (a : A) (F : TracialState A → ℝ≥0∞) (hF : Continuous F) :
    IsOpen {τ : TracialState A | F τ < normalizedRootRank τ a} := by
  have hopen : IsOpen (⋃ n : ℕ, {τ : TracialState A |
      F τ < ENNReal.ofReal (τ.functional (normalizedRoot a n)).re}) :=
    isOpen_iUnion fun n => isOpen_lt hF (ENNReal.continuous_ofReal.comp
      (Complex.continuous_re.comp (TracialState.continuous_eval (normalizedRoot a n))))
  convert hopen using 2
  ext τ
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, normalizedRootRank, lt_iSup_iff]

theorem uniform_normalizedRootTrace_index (a : A) (ha : 0 ≤ a)
    (F : TracialState A → ℝ≥0∞) (hF : Continuous F)
    (hgap : ∀ τ, F τ < normalizedRootRank τ a) :
    ∃ n : ℕ, ∀ τ, F τ < ENNReal.ofReal (τ.functional (normalizedRoot a n)).re := by
  apply uniform_strict_index F (fun n τ => ENNReal.ofReal (τ.functional (normalizedRoot a n)).re)
  · intro n
    exact isOpen_lt hF (ENNReal.continuous_ofReal.comp
      (Complex.continuous_re.comp (TracialState.continuous_eval (normalizedRoot a n))))
  · intro τ i j hij
    exact ENNReal.ofReal_le_ofReal
      (Complex.le_def.mp (τ.functional.monotone (normalizedRoot_monotone a ha hij))).1
  · exact hgap
end CuntzPureness

end OAI
