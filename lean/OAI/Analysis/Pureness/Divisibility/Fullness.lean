import OAI.Analysis.Pureness.Divisibility.FullnessDensity
import OAI.Analysis.Pureness.Divisibility.FullnessPositiveSum
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
namespace CuntzPureness
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem fullness (hsimple : TopologicallySimple A) (h : A) (hh : 0 ≤ h) (hne : h ≠ 0) :
    ∃ n : ℕ, ∃ s : Fin n → A, ∑ i, star (s i) * h * s i = 1 := by
  obtain ⟨l, hl⟩ := exists_invertible_finiteIdealSum hsimple h hne
  have hrep : finiteIdealSum h l = ∑ i : Fin l.length, (l.get i).1 * h * (l.get i).2 := by
    have heq := congrArg (fun v : List (A × A) => finiteIdealSum h v) (List.ofFn_get l)
    simpa only [finiteIdealSum, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using heq.symm
  have hunit : IsUnit (∑ i : Fin l.length, star (l.get i).2 * h * (l.get i).2) :=
    invertible_positive_sum_of_invertible_sum h hh
      (fun i : Fin l.length => (l.get i).1) (fun i => (l.get i).2) (hrep ▸ hl)
  obtain ⟨s, hs⟩ := normalize_fullness_sum Finset.univ h hh (fun i : Fin l.length => (l.get i).2) hunit
  exact ⟨l.length, s, hs⟩

theorem exists_positive_trace_transfer (hsimple : TopologicallySimple A)
    (h p : A) (hh : 0 ≤ h) (hne : h ≠ 0) (hp : 0 ≤ p) :
    ∃ c : A, c ∈ Set.range (fun z : A => CFC.sqrt h * z * CFC.sqrt h) ∧
      0 ≤ c ∧ ∀ (τ : A →+ ℂ),
      (∀ a b : A, τ (a * b) = τ (b * a)) → τ c = τ p := by
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hne
  exact ⟨traceTransfer Finset.univ (CFC.sqrt h) p s,
    ⟨∑ i, s i * p * star (s i), (traceTransfer_eq_sandwich Finset.univ _ p s).symm⟩,
    sqrt_trace_transfer Finset.univ h p hh hp s hs⟩
end CuntzPureness

end OAI
