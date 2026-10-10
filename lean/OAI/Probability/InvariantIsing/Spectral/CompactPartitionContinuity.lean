import OAI.Probability.InvariantIsing.Spectral.CompactSpectralPartition
import OAI.Probability.InvariantIsing.Spectral.MeasureVariationalContinuity

namespace OAI

/-! The finite positive-mass partition values converge to the compact spectral value. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

lemma compact_partition_laws_tendsto (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (δ : ℕ → ℝ) (D : (k : ℕ) → CompactSpectralPartition ν a b (δ k))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => (D k).law) atTop (𝓝 ν) := by
  have hh := spectral_quantization_weak ν
    (fun k => spectralBallQuantizer (D k).center (D k).radius a)
    (fun k => measurable_spectralBallQuantizer _ _ _) δ hδ (fun k => (D k).quantizer_close)
  apply hh.congr
  intro k
  apply Subtype.ext
  exact (D k).law_eq_map.symm

lemma compact_partition_edges_tendsto (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (δ : ℕ → ℝ) (D : (k : ℕ) → CompactSpectralPartition ν a b (δ k))
    (hab : a ≤ b) (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => (D k).edge) atTop (𝓝 b) := by
  have hlo k : b-δ k ≤ (D k).edge := by linarith [(D k).endpoint_bounds ha hb]
  have hhi k : (D k).edge ≤ b := ((D k).value_mem hab (D k).upper).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using tendsto_const_nhds.sub hδ)
    tendsto_const_nhds hlo hhi

lemma compact_partition_variational_tendsto (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (δ : ℕ → ℝ) (D : (k : ℕ) → CompactSpectralPartition ν a b (δ k))
    (hab : a ≤ b) (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => (variationalFunctional (measureR ((D k).law : Measure ℝ) (D k).edge)).toReal)
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  let K := |a|+|b|+1
  have hK : 0 < K := by dsimp [K]; positivity
  have haK : -K ≤ a := by dsimp [K]; linarith [neg_abs_le a,abs_nonneg b]
  have hbK : b ≤ K := by dsimp [K]; linarith [le_abs_self b,abs_nonneg a]
  exact measureVariational_tendsto_weak (fun k => (D k).law) ν
    (fun k => (D k).edge) b (compact_partition_laws_tendsto ν a b δ D hδ)
    (compact_partition_edges_tendsto ν a b δ D hab ha hb hδ) hK hbK
    (fun k => (((D k).value_mem hab (D k).upper).2).trans hbK)
    (fun k => ((D k).law_support hab).mono (fun _ hx => ⟨haK.trans hx.1,hx.2⟩))
    (by
      filter_upwards [(ν : Measure ℝ).support_mem_ae] with x hx
      exact ⟨haK.trans (hbound hx).1,(hbound hx).2⟩)

end InvariantIsing

end

end OAI
