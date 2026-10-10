import OAI.Probability.BenjaminiSchramm.PeakCorrelationAveraging

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma probability_complement_correlation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C B : Set Ω)
    (hB : MeasurableSet B) (hneg : μ (C ∩ B) ≤ μ C * μ B) :
    μ C * μ Bᶜ ≤ μ (C ∩ Bᶜ) := by
  apply ENNReal.le_of_add_le_add_left (measure_ne_top μ (C ∩ B))
  calc
    μ (C ∩ B) + μ C * μ Bᶜ ≤ μ C * μ B + μ C * μ Bᶜ :=
      add_le_add hneg le_rfl
    _ = μ C := by rw [←mul_add,prob_add_prob_compl hB,mul_one]
    _ = μ (C ∩ B) + μ (C ∩ Bᶜ) := by
      simpa only [Set.sdiff_eq] using (measure_inter_add_sdiff (μ := μ) C hB).symm

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem connection_avoiding_hit_complement_correlation (p : unitInterval)
    (I J : Set E) (hJI : J ⊆ I) (u w : V) (A T : Set V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) u).Finite) :
    law p (connectionAvoidingHit G I J u w T) * law p (restrictedSetHit G I A T)ᶜ ≤
      law p (connectionAvoidingHit G I J u w T ∩ (restrictedSetHit G I A T)ᶜ) :=
  probability_complement_correlation (law p) _ _
    (measurableSet_restrictedSetHit G I A T)
    (connection_avoiding_hit_negative_correlation G p I J hJI u w A T hfin)

end Percolation.BenjaminiSchramm

end

end OAI
