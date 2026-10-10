import OAI.MeasureTheory.Falconer.Measures.PairCorePruning
import OAI.MeasureTheory.Falconer.Estimates.Availability

namespace OAI

/-! # Restrict pair filters to the original supports without losing mass -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def supportPair (μ ν : ProbabilityMeasure (Space d)) : Set (Space d × Space d) :=
  (μ : Measure (Space d)).support ×ˢ (ν : Measure (Space d)).support

theorem supportPair_measurable (μ ν : ProbabilityMeasure (Space d)) :
    MeasurableSet (supportPair μ ν) :=
  Measure.isClosed_support.measurableSet.prod Measure.isClosed_support.measurableSet

theorem supportPair_compl_null (μ ν : ProbabilityMeasure (Space d)) :
    ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (supportPair μ ν)ᶜ = 0 :=
  product_core_compl_null _ _ _ _ Measure.measure_compl_support Measure.measure_compl_support

theorem supportPair_inter_mass (μ ν : ProbabilityMeasure (Space d))
    (G : Set (Space d × Space d)) :
    ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (G ∩ supportPair μ ν) =
      ((μ : Measure (Space d)).prod (ν : Measure (Space d))) G :=
  measure_inter_conull (supportPair_compl_null μ ν)

theorem supportPair_iInter_mass (μ ν : ProbabilityMeasure (Space d))
    (Γ : ℕ → Set (Space d × Space d)) :
    ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (⋂ N, Γ N ∩ supportPair μ ν) =
      ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (⋂ N, Γ N) := by
  have heq : (⋂ N, Γ N ∩ supportPair μ ν) = (⋂ N, Γ N) ∩ supportPair μ ν := by
    ext z
    simp only [mem_iInter,mem_inter_iff]
    exact ⟨fun h => ⟨fun N => (h N).1,(h 0).2⟩,fun h N => ⟨h.1 N,h.2⟩⟩
  rw [heq,supportPair_inter_mass]

end Falconer

end OAI
