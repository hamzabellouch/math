import OAI.Probability.BenjaminiSchramm.ClusterExposure

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem lintegral_eq_sum_finite_clusters (p : unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite) (F : Set V → ℝ≥0∞) :
    (∫⁻ ω, F (G.cluster ω x) ∂G.law p) =
      ∑' S : Finset V, G.law p {ω | G.cluster ω x = (S : Set V)} * F (S : Set V) := by
  have heq : (fun ω => F (G.cluster ω x)) =ᵐ[G.law p]
      (fun ω => ∑' S : Finset V, if G.cluster ω x = (S : Set V) then F (S : Set V) else 0) := by
    filter_upwards [hfin] with ω hω
    rw [tsum_eq_single hω.toFinset (fun S hS => by
      apply ite_eq_right
      intro hc
      exact hS (Finset.coe_injective (hc.symm.trans hω.coe_toFinset.symm)))]
    rw [ite_eq_left hω.coe_toFinset.symm, hω.coe_toFinset]
  rw [lintegral_congr_ae heq,lintegral_tsum]
  · apply tsum_congr
    intro S
    simpa only [Set.indicator,Set.mem_ofPred_eq,mul_comm] using
      lintegral_indicator_const (G.measurableSet_exactCluster x (S : Set V)) (F (S : Set V))
  · intro S
    exact (measurable_const.ite (G.measurableSet_exactCluster x (S : Set V))
      measurable_const).aemeasurable

end CriticalPercolation.BondGraph

end

end OAI
