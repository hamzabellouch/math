import OAI.Probability.InvariantIsing.Spectral.CompactPartitionContinuity
import OAI.Probability.InvariantIsing.Spectral.MeasureMagneticContinuity

namespace OAI

/-! Magnetic variational convergence for finite positive spectral partitions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma compact_partition_magnetic_tendsto (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (δ : ℕ → ℝ) (D : (k : ℕ) → CompactSpectralPartition ν a b (δ k))
    (hab : a ≤ b) (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b) (hδ : Tendsto δ atTop (𝓝 0))
    {A : Type*} [Fintype A] (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) :
    Tendsto (fun k => (finiteMagneticFunctional (measureR ((D k).law : Measure ℝ) (D k).edge) γ c).toReal)
      atTop (𝓝 (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) γ c).toReal) := by
  let K := |a|+|b|+1
  have hK : 0 < K := by dsimp [K]; positivity
  have haK : -K ≤ a := by dsimp [K]; linarith [neg_abs_le a,abs_nonneg b]
  have hbK : b ≤ K := by dsimp [K]; linarith [le_abs_self b,abs_nonneg a]
  exact measureMagnetic_tendsto_weak (fun k => (D k).law) ν
    (fun k => (D k).edge) b (compact_partition_laws_tendsto ν a b δ D hδ)
    (compact_partition_edges_tendsto ν a b δ D hab ha hb hδ) hK hbK
    (fun k => (((D k).value_mem hab (D k).upper).2).trans hbK)
    (fun k => ((D k).law_support hab).mono (fun _ hx => ⟨haK.trans hx.1,hx.2⟩))
    (by
      filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
      exact ⟨haK.trans (hbound hx).1,(hbound hx).2⟩) γ c hγ hγsum

end InvariantIsing

end

end OAI
