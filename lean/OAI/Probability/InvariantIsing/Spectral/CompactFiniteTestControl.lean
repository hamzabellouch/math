import OAI.Probability.InvariantIsing.Spectral.ResolventMeasureUniqueness
import Mathlib.MeasureTheory.Measure.Prokhorov

namespace OAI

/-! Finitely many separating tests control a continuous image of a compact space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace InvariantIsing

theorem compact_finite_test_control {X ι Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] (F : ι → X → ℝ) (hF : ∀ i, Continuous (F i))
    (hsep : ∀ x y, (∀ i, F i x = F i y) → x = y)
    (G : X → Y) (hG : Continuous G) (x₀ : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι, ∃ δ : ι → ℝ, (∀ i, 0 < δ i) ∧
      ∀ x, (∀ i ∈ s, dist (F i x) (F i x₀) < δ i) → dist (G x) (G x₀) < ε := by
  classical
  let E : X → (ι → ℝ) := fun x i => F i x
  have hE : Continuous E := continuous_pi hF
  have he : Function.Injective E := fun x y h => hsep x y (congrFun h)
  have hi := (hE.isClosedEmbedding he).isEmbedding.isInducing
  have hu : G ⁻¹' Metric.ball (G x₀) ε ∈ 𝓝 x₀ :=
    hG.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  rw [hi.nhds_eq_comap] at hu
  obtain ⟨V,hV,hVU⟩ := Filter.mem_comap.mp hu
  rw [nhds_pi] at hV
  obtain ⟨s,W,hW,hWV⟩ := Filter.mem_pi'.mp hV
  choose δ hδ hd using fun i => Metric.mem_nhds_iff.mp (hW i)
  refine ⟨s,δ,hδ,fun x hx => ?_⟩
  apply hVU
  apply hWV
  intro i hi'
  exact hd i (hx i hi')

end InvariantIsing

end

end OAI
