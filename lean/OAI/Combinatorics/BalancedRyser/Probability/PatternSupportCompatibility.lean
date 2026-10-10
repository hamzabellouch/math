import OAI.Combinatorics.BalancedRyser.Probability.PatternIntegrability
import OAI.Combinatorics.BalancedRyser.Probability.PatternPrefixSupport

namespace OAI

namespace Balanced.PatternModel

attribute [local instance] Classical.propDecidable

variable (P : PatternModel)

lemma additionalSupport_eq_freshPrefixSupport (K₀ : Finset P.Color)
    (pre : List P.Label) :
    P.additionalSupport K₀ pre = P.freshPrefixSupport K₀ pre := by
  classical
  ext c
  simp only [additionalSupport, Finset.mem_biUnion, List.mem_toFinset,
    Finset.mem_sdiff, P.mem_freshPrefixSupport_iff]

lemma card_additionalSupport_le (K₀ : Finset P.Color) (pre : List P.Label)
    (r : ℕ) (hr : ∀ a ∈ pre, (P.support a).card ≤ r) :
    (P.additionalSupport K₀ pre).card ≤ pre.length * r := by
  rw [P.additionalSupport_eq_freshPrefixSupport]
  exact P.card_freshPrefixSupport_le K₀ pre r hr

lemma disjoint_additionalSupport_initial (K₀ : Finset P.Color)
    (pre : List P.Label) : Disjoint (P.additionalSupport K₀ pre) K₀ := by
  rw [P.additionalSupport_eq_freshPrefixSupport]
  exact P.disjoint_freshPrefixSupport_initial K₀ pre

lemma overlapCount_additionalSupport (K₀ : Finset P.Color)
    (pre : List P.Label) (ω : P.Sample) :
    P.overlapCount K₀ (P.additionalSupport K₀ pre) ω =
      ∑ a, if PatternMoments.supportOverlap P.support K₀ pre a then
        P.indicator a ω else 0 := by
  classical
  rw [P.additionalSupport_eq_freshPrefixSupport]
  exact P.overlapCount_freshPrefixSupport K₀ pre ω

lemma positiveProduct_dependsOn_freshPrefix (K₀ : Finset P.Color)
    (x : P.Sample) (pre : List P.Label) (ω η : P.Sample)
    (h : ∀ c ∈ K₀ ∪ P.freshPrefixSupport K₀ pre, ω c = η c) :
    P.positiveProduct K₀ x pre ω = P.positiveProduct K₀ x pre η := by
  apply P.positiveProduct_dependsOn K₀ x pre ω η
  simpa only [P.additionalSupport_eq_freshPrefixSupport] using h

end Balanced.PatternModel

end OAI
