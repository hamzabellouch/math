import OAI.Probability.InvariantIsing.Spectral.CompactFiniteTestControl

namespace OAI

/-! Convergence in measure from separating continuous tests on a compact state space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace InvariantIsing

theorem compact_tests_tendstoInMeasure {X ι Y Ω : Type*} [TopologicalSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] [MeasurableSpace Ω] (P : Measure Ω)
    (F : ι → X → ℝ) (hF : ∀ i, Continuous (F i))
    (hsep : ∀ x y, (∀ i, F i x = F i y) → x = y)
    (G : X → Y) (hG : Continuous G) (x₀ : X) (Z : ℕ → Ω → X)
    (hZ : ∀ i, TendstoInMeasure P (fun n ω => F i (Z n ω)) atTop (fun _ => F i x₀)) :
    TendstoInMeasure P (fun n ω => G (Z n ω)) atTop (fun _ => G x₀) := by
  classical
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  obtain ⟨s,δ,hδ,hcontrol⟩ := compact_finite_test_control F hF hsep G hG x₀ hε
  have hb (n : ℕ) : {ω | ε ≤ dist (G (Z n ω)) (G x₀)} ⊆
      ⋃ i ∈ s, {ω | δ i ≤ dist (F i (Z n ω)) (F i x₀)} := by
    intro ω hω
    have hh : ∃ i ∈ s, δ i ≤ dist (F i (Z n ω)) (F i x₀) := by
      by_contra! hh
      exact (not_lt_of_ge hω) (hcontrol (Z n ω) hh)
    obtain ⟨i,hi,hii⟩ := hh
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hii⟩⟩
  have ht := tendsto_finsetSum s (fun i _ => (tendstoInMeasure_iff_dist.mp (hZ i)) (δ i) (hδ i))
  have ht' : Tendsto (fun n => ∑ i ∈ s, P {ω | δ i ≤ dist (F i (Z n ω)) (F i x₀)})
      atTop (𝓝 0) := by simpa only [Finset.sum_const_zero] using ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht'
    (fun _ => bot_le) (fun n => (measure_mono (hb n)).trans (measure_biUnion_finset_le _ _))

end InvariantIsing

end

end OAI
