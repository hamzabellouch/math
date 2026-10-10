import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import OAI.Analysis.IrrationalRotation.Analysis.LusinCompact

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Invariant233.CompactTransfer

theorem measure_compl_le_of_tendsto {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {L : Filter ι} [L.NeBot]
    {ν : FiniteMeasure X} {νs : ι → FiniteMeasure X}
    (hν : Tendsto νs L (𝓝 ν)) {K : Set X} (hK : IsClosed K)
    {ε : ℝ≥0∞} (hbound : ∀ᶠ i in L, (νs i : Measure X) Kᶜ ≤ ε) :
    (ν : Measure X) Kᶜ ≤ ε := by
  have hmass : Tendsto (fun i => (νs i : Measure X) Set.univ) L
      (𝓝 ((ν : Measure X) Set.univ)) := by
    simpa only [← FiniteMeasure.ennreal_mass, Function.comp_def] using
      ENNReal.continuous_coe.continuousAt.tendsto.comp hν.mass
  have hparts : ∀ᶠ i in L,
      (νs i : Measure X) Set.univ ≤ (νs i : Measure X) K + ε := by
    filter_upwards [hbound] with i hi
    rw [← measure_add_measure_compl hK.measurableSet]
    exact add_le_add le_rfl hi
  have hlim := Filter.limsup_le_limsup hparts
  rw [hmass.limsup_eq,
    limsup_add_const L (fun i => (νs i : Measure X) K) ε
      (by isBoundedDefault) (by isBoundedDefault)] at hlim
  have htotal := hlim.trans (add_le_add
    (FiniteMeasure.limsup_measure_closed_le_of_tendsto hν hK) le_rfl)
  rw [measure_compl hK.measurableSet (measure_ne_top _ _), tsub_le_iff_right]
  simpa only [add_comm] using htotal

theorem ae_mem_of_closed_approximation {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {L : Filter ι} [L.NeBot]
    {ν : FiniteMeasure X} {νs : ι → FiniteMeasure X}
    (hν : Tendsto νs L (𝓝 ν)) {S : Set X}
    (happrox : ∀ ε : ℝ≥0, 0 < ε → ∃ K : Set X,
      IsClosed K ∧ K ⊆ S ∧ ∀ᶠ i in L, (νs i : Measure X) Kᶜ ≤ ε) :
    ∀ᵐ x ∂(ν : Measure X), x ∈ S := by
  apply ae_iff.mpr
  change (ν : Measure X) Sᶜ = 0
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨K, hK, hKS, hbound⟩ := happrox ε hε
  simpa using
    (measure_mono (Set.compl_subset_compl.mpr hKS)).trans
      (measure_compl_le_of_tendsto hν hK hbound)

theorem ae_relation_of_uniform_marginals {X ι κ : Type*} {Y : κ → Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [Countable κ] [∀ k, TopologicalSpace (Y k)]
    [∀ k, SecondCountableTopology (Y k)]
    [∀ k, MeasurableSpace (Y k)] [∀ k, OpensMeasurableSpace (Y k)]
    (μ : Measure X) [IsFiniteMeasure μ]
    {f : ∀ k, X → Y k} (hf : ∀ k, Measurable (f k))
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    {S : Set (X × X)}
    (hclosed : ∀ K : Set X, IsCompact K →
      (∀ k, ContinuousOn (f k) K) → IsClosed ((K ×ˢ K) ∩ S))
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i,
        (νs i : Measure (X × X)) (A ×ˢ Set.univ) +
        (νs i : Measure (X × X)) (Set.univ ×ˢ A) ≤ ε)
    (hS : ∀ i, ∀ᵐ z ∂(νs i : Measure (X × X)), z ∈ S) :
    ∀ᵐ z ∂(ν : Measure (X × X)), z ∈ S := by
  apply ae_mem_of_closed_approximation hν
  intro ε hε
  obtain ⟨δ, hδ, hδsmall⟩ := hsmall ε hε
  obtain ⟨K, hK, hμK, hcont⟩ := exists_isCompact_forall_continuousOn μ hf hδ
  refine ⟨(K ×ˢ K) ∩ S, hclosed K hK hcont, Set.inter_subset_right,
    Filter.Eventually.of_forall ?_⟩
  intro i
  have hsub : ∀ᵐ z ∂(νs i : Measure (X × X)),
      z ∈ ((K ×ˢ K) ∩ S)ᶜ → z ∈ (K ×ˢ K)ᶜ := by
    filter_upwards [hS i] with z hz
    intro hzbad hzK
    exact hzbad ⟨hzK, hz⟩
  apply (measure_mono_ae hsub).trans
  rw [Set.compl_prod_eq_union]
  exact (measure_union_le _ _).trans
    (hδsmall Kᶜ hK.isClosed.measurableSet.compl hμK i)

end Invariant233.CompactTransfer

end OAI
