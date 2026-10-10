import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336

theorem clopen_measure_eq_of_mapClusterPt
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    {α : Type*} {F : Filter α} {μs : α → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} (hμ : MapClusterPt μ F μs)
    {S : Set E} (hS : IsClopen S) {L : ℝ≥0∞}
    (hL : Tendsto (fun a => (μs a : Measure E) S) F (𝓝 L)) :
    (μ : Measure E) S = L := by
  let G := 𝓝 μ ⊓ Filter.map μs F
  have : G.NeBot := hμ.neBot
  have ht : Tendsto (id : ProbabilityMeasure E → ProbabilityMeasure E) G (𝓝 μ) := by
    change G ≤ 𝓝 μ
    exact inf_le_left
  have hv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto ht hS
  have hev : Tendsto (fun ν : ProbabilityMeasure E => (ν : Measure E) S) G
      (𝓝 ((μ : Measure E) S)) := by
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, id_eq,
      Function.comp_def] using (ENNReal.continuous_coe.tendsto _).comp hv
  have hl : Tendsto (fun ν : ProbabilityMeasure E => (ν : Measure E) S)
      (Filter.map μs F) (𝓝 L) := tendsto_map'_iff.mpr hL
  exact tendsto_nhds_unique hev (hl.mono_left inf_le_right)

theorem exists_probabilityMeasure_of_clopen_limits
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [T2Space E] [CompactSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    {ι : Type*} (μn : ℕ → ProbabilityMeasure E)
    (S : ι → Set E) (hS : ∀ i, IsClopen (S i)) (L : ι → ℝ≥0∞)
    (hL : ∀ i, Tendsto (fun n => (μn n : Measure E) (S i)) atTop (𝓝 (L i))) :
    ∃ μ : ProbabilityMeasure E, ∀ i, (μ : Measure E) (S i) = L i := by
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace (Filter.map μn atTop)
  exact ⟨μ, fun i => clopen_measure_eq_of_mapClusterPt hμ (hS i) (hL i)⟩

theorem exists_probabilityMeasure_tendsto_of_clopen_limits
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [T2Space E] [CompactSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    {ι : Type*} (μn : ℕ → ProbabilityMeasure E)
    (S : ι → Set E) (hS : ∀ i, IsClopen (S i))
    (hsep : ∀ μ ν : ProbabilityMeasure E,
      (∀ i, (μ : Measure E) (S i) = (ν : Measure E) (S i)) → μ = ν)
    (L : ι → ℝ≥0∞)
    (hL : ∀ i, Tendsto (fun n => (μn n : Measure E) (S i)) atTop (𝓝 (L i))) :
    ∃ μ : ProbabilityMeasure E,
      (∀ i, (μ : Measure E) (S i) = L i) ∧ Tendsto μn atTop (𝓝 μ) := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_clopen_limits μn S hS L hL
  refine ⟨μ, hμ, tendsto_nhds_of_unique_mapClusterPt (fun ν hν => ?_)⟩
  exact hsep ν μ fun i =>
    (clopen_measure_eq_of_mapClusterPt hν (hS i) (hL i)).trans (hμ i).symm

theorem isClopen_boolCylinder {I : Type*} (A B : Finset I) :
    IsClopen {x : I → Bool |
      (∀ i ∈ A, x i = true) ∧ (∀ i ∈ B, x i = false)} := by
  have h (s : Finset I) (b : Bool) :
      IsClopen {x : I → Bool | ∀ i ∈ s, x i = b} := by
    have heq : {x : I → Bool | ∀ i ∈ s, x i = b} =
        ⋂ i ∈ s, (fun x : I → Bool => x i) ⁻¹' {b} := by
      ext x
      simp
    rw [heq]
    exact isClopen_biInter_finset fun i _ =>
      (isClopen_discrete ({b} : Set Bool)).preimage (continuous_apply i)
  exact (h A true).inter (h B false)

theorem exists_probabilityMeasure_of_boolCylinder_limits
    {I : Type*} [Countable I]
    (μn : ℕ → ProbabilityMeasure (I → Bool))
    (L : Finset I → Finset I → ℝ≥0∞)
    (hL : ∀ A B, Tendsto
      (fun n => (μn n : Measure (I → Bool))
        {x | (∀ i ∈ A, x i = true) ∧ (∀ i ∈ B, x i = false)})
      atTop (𝓝 (L A B))) :
    ∃ μ : ProbabilityMeasure (I → Bool), ∀ A B,
      (μ : Measure (I → Bool))
        {x | (∀ i ∈ A, x i = true) ∧ (∀ i ∈ B, x i = false)} = L A B := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_clopen_limits μn
    (fun p : Finset I × Finset I =>
      {x | (∀ i ∈ p.1, x i = true) ∧ (∀ i ∈ p.2, x i = false)})
    (fun p => isClopen_boolCylinder p.1 p.2)
    (fun p => L p.1 p.2) (fun p => hL p.1 p.2)
  exact ⟨μ, fun A B => hμ (A, B)⟩

end Problem336

end

end OAI
