import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

instance discreteOnePoint_countable (H : Type*) [Countable H] : Countable (OnePoint H) := by
  unfold OnePoint
  infer_instance

instance discreteOnePoint_firstCountable (H : Type*) [TopologicalSpace H]
    [DiscreteTopology H] [Countable H] : FirstCountableTopology (OnePoint H) := by
  constructor
  intro x
  induction x using OnePoint.rec with
  | coe x =>
    rw [OnePoint.nhds_coe_eq, nhds_discrete]
    infer_instance
  | infty =>
    rw [OnePoint.nhds_infty_eq, coclosedCompact_eq_cocompact, cocompact_eq_cofinite]
    have : (cofinite : Filter H).IsCountablyGenerated :=
      (show (cofinite : Filter H).HasCountableBasis Set.Finite (fun s => sᶜ) from
        ⟨Filter.hasBasis_cofinite, Set.Countable.ofPred_finite⟩).isCountablyGenerated
    infer_instance

instance discreteOnePoint_secondCountable (H : Type*) [TopologicalSpace H]
    [DiscreteTopology H] [Countable H] : SecondCountableTopology (OnePoint H) := inferInstance

abbrev Label := ℤ × ℕ
abbrev MarkSpace := ℕ∞ × ℕ∞ × ℝ≥0∞
abbrev EpisodeArray (H R : Type*) :=
  (ℤ → MarkSpace) × ((Label × Label) → OnePoint H) ×
    ((ℤ × Label × H) → Set.Icc (0:ℝ) 1) ×
    ((ℤ × ℕ × ℕ × ℕ × H) → R)

variable {H R : Type*}
  [TopologicalSpace H] [DiscreteTopology H] [Countable H]
  [TopologicalSpace R] [CompactSpace R] [T2Space R] [SecondCountableTopology R]

instance array_compact : CompactSpace (EpisodeArray H R) := inferInstance
instance array_secondCountable : SecondCountableTopology (EpisodeArray H R) := inferInstance
instance array_t2 : T2Space (EpisodeArray H R) := by
  have : T2Space (OnePoint H) := inferInstance
  have : T2Space MarkSpace := inferInstance
  unfold EpisodeArray
  infer_instance
instance array_metrizable : MetrizableSpace (EpisodeArray H R) := inferInstance

def shift (a : EpisodeArray H R) : EpisodeArray H R :=
  ⟨fun i => a.1 (i+1),
   (fun p => a.2.1 ((p.1.1+1,p.1.2),(p.2.1+1,p.2.2))),
   (fun p => a.2.2.1 (p.1+1,(p.2.1.1+1,p.2.1.2),p.2.2)),
   (fun p => a.2.2.2 (p.1+1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2))⟩

omit [DiscreteTopology H] [Countable H] [CompactSpace R] [T2Space R]
  [SecondCountableTopology R] in
lemma shift_continuous : Continuous (shift : EpisodeArray H R → EpisodeArray H R) := by
  unfold shift
  fun_prop

end DirectionalTransience.StationaryCompact

end

end OAI
