import OAI.Analysis.FiniteFactor.Coupling.Infinite

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

def orderedPairs : Set (ℝ × ℝ) := {xy | xy.1 ≤ xy.2}

theorem orderedPairs_measurable : MeasurableSet orderedPairs :=
  measurableSet_le measurable_fst measurable_snd

theorem componentPair_ordered (i : Fin 6) : p.pairComponentLaw i orderedPairs = 1 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · change (unitIntervalMeasure.map (fun t => (t,t))) orderedPairs = 1
    have hm : Measurable (fun t : ℝ => (t,t)) := measurable_id.prodMk measurable_id
    rw [Measure.map_apply hm orderedPairs_measurable]
    simp [orderedPairs]
  · change ((p.endpointComponentLaw false k).prod (p.endpointComponentLaw true k)) orderedPairs = 1
    have hU := p.endpointComponentLaw_of_contains false k (Set.Subset.refl _)
    have hV := p.endpointComponentLaw_of_contains true k (Set.Subset.refl _)
    have hsub : (p.endpointInterval false k ×ˢ p.endpointInterval true k) ⊆ orderedPairs := by
      intro xy hxy
      have h₁ : xy.1 < p.leftLength k := hxy.1.2
      have h₂ : 1-p.rightLength k ≤ xy.2 := hxy.2.1
      have hlen := p.lengths_sum_le k
      change xy.1 ≤ xy.2
      linarith
    apply le_antisymm prob_le_one
    have h := measure_mono (μ := (p.endpointComponentLaw false k).prod (p.endpointComponentLaw true k)) hsub
    rw [Measure.prod_prod, hU, hV, mul_one] at h
    exact h

theorem coupling_ordered : p.coupling orderedPairs = 1 := by
  rw [p.coupling_eq_sum, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, p.componentPair_ordered, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.labelMass_nonneg i), p.labelMass_sum]
  simp

theorem labelledCoupling_ordered : p.labelledCoupling {z | z.2.1 ≤ z.2.2} = 1 := by
  have h := p.coupling_ordered
  rw [coupling, Measure.map_apply measurable_snd orderedPairs_measurable] at h
  exact h

/-- All infinitely many coordinates are ordered under the actual augmented law. -/
theorem productCoupling_ordered (p : ℕ → CouplingParameters) :
    productCoupling p {ω | ∀ i, (ω i).2.1 ≤ (ω i).2.2} = 1 := by
  have hset : {ω : CouplingSample | ∀ i, (ω i).2.1 ≤ (ω i).2.2} =
      Set.pi Set.univ (fun _ : ℕ => {z : Fin 6 × (ℝ × ℝ) | z.2.1 ≤ z.2.2}) := by
    ext ω
    simp
  rw [hset, productCoupling, Measure.infinitePi_pi_univ]
  · simp [labelledCoupling_ordered]
  · intro i
    exact orderedPairs_measurable.preimage measurable_snd

end CouplingParameters
end
end FiniteFactor

end OAI
