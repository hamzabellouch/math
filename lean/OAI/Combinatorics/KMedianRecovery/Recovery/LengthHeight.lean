import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LeafOrder
import OAI.Combinatorics.KMedianRecovery.Recovery.DecisionOps

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open RationalHeight
variable {X : Type*} [DecidableEq X]

def heightBudget (b : ℚ) (precision h : ℕ) : ℕ :=
  4*h+2*PriceBisection.iterations 0 b precision+3

lemma range_height (f : ℚ → ℕ) (k precision : ℕ) (b : ℚ) (h : ℕ) (hb : Height b h) :
    Height (range f k precision b).1 (heightBudget b precision h) ∧
    Height (range f k precision b).2 (heightBudget b precision h) := by
  unfold range
  split
  · have hh := PriceBisection.iterate_height (zero h) hb (fun s=>f (b-s)) k
      (PriceBisection.iterations 0 b precision)
    rw [←PriceBisection.search_eq_iterate] at hh
    exact ⟨by convert hb.sub hh.2 using 1; simp [heightBudget]; omega,
      by convert hb.sub hh.1 using 1; simp [heightBudget]; omega⟩
  · have hh := PriceBisection.iterate_height (zero h) hb f k
      (PriceBisection.iterations 0 b precision)
    rw [←PriceBisection.search_eq_iterate] at hh
    exact ⟨hh.1.mono (by unfold heightBudget; omega),hh.2.mono (by unfold heightBudget; omega)⟩

def Result.Bounded (h : ℕ) : Result X → Prop
  | .success s _ => Height s h
  | .bracket l u _ _ => Height l h ∧ Height u h

lemma run_height (F Q : Finset X) (leaf : ℚ → X) (complete : ℚ → List (List X))
    (T U : List (List X)) (b : ℚ) (k precision h : ℕ) (hb : Height b h) :
    (run F Q leaf complete T U b k precision).Bounded (heightBudget b precision h) := by
  have hh := range_height (count F Q leaf complete T U b) k precision b h hb
  dsimp only [run]
  split_ifs
  · exact hh.1
  · exact hh.2
  · exact hh

end MetricKMedianRecovery.CanonicalLengthSearch

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence RationalLeaves RationalHeight CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}
lemma run_height (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (Q : Finset (Label V)) (v lam b : ℚ) (q n k key precision h : ℕ)
    (H : List (Label V)) (T U : List (List (Label V))) (J : Plan (Label V)) (hb : Height b h) :
    (run loc distance F Q v lam b q n k key precision H T U J).Bounded
      (CanonicalLengthSearch.heightBudget b precision h) := by
  dsimp only [run]
  split
  · exact zero _
  · exact CanonicalLengthSearch.run_height _ _ _ _ _ _ _ _ _ _ hb
end MetricKMedianRecovery.CanonicalSensitiveEndpoint

end OAI
