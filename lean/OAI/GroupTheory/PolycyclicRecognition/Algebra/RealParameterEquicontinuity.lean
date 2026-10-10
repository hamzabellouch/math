import OAI.GroupTheory.PolycyclicRecognition.Analysis.AsymptoticEquicontinuity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! # A single modulus for all nonnegative chart scales -/

namespace PolycyclicRecognition

open Filter Set
open scoped Topology

/-- Joint continuity controls a compact initial interval of scales; the
joint limit at infinity controls the remaining scales. -/
theorem uniform_nonnegative_parameter_of_joint_limit
    {X : Type*} [TopologicalSpace X] (E : ℝ → X → ℝ) (x₀ : X)
    (hE : Continuous (fun p : ℝ × X => E p.1 p.2))
    (hzero : ∀ r, E r x₀ = 0)
    (htail : Tendsto (fun p : ℝ × X => E p.1 p.2)
      (atTop ×ˢ 𝓝 x₀) (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x in 𝓝 x₀, ∀ r, 0 ≤ r → E r x < ε := by
  intro ε hε
  obtain ⟨s, hs, U, hU, htailU⟩ :=
    mem_prod_iff.mp (htail.eventually (gt_mem_nhds hε))
  obtain ⟨R, hR⟩ := eventually_atTop.mp hs
  have hhead : {p : ℝ × X | E p.1 p.2 < ε} ∈
      (𝓝ˢ (Icc (0 : ℝ) (max R 0))) ×ˢ 𝓝 x₀ := by
    apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max R 0))).mem_nhdsSet_prod_of_forall
    intro r _
    have hh := (hE.tendsto (r, x₀)).eventually
      (gt_mem_nhds (show E r x₀ < ε by rw [hzero]; exact hε))
    change {p : ℝ × X | E p.1 p.2 < ε} ∈ 𝓝 (r, x₀) at hh
    rwa [nhds_prod_eq] at hh
  obtain ⟨V, hV, U', hU', hheadU⟩ := mem_prod_iff.mp hhead
  have hKV : Icc (0 : ℝ) (max R 0) ⊆ V := subset_of_mem_nhdsSet hV
  filter_upwards [hU, hU'] with x hx hx'
  intro r hr
  by_cases h : r ≤ max R 0
  · exact hheadU (show (r, x) ∈ V ×ˢ U' from ⟨hKV ⟨hr, h⟩, hx'⟩)
  · exact htailU (show (r, x) ∈ s ×ˢ U from
      ⟨hR r ((le_max_left _ _).trans (le_of_not_ge h)), hx⟩)

/-- The same metric modulus controls all maps and all nonnegative scales,
with no choice of a scale sequence in the compact family. -/
theorem equicontinuous_nonnegative_parameter_of_joint_error
    {X W A : Type*} [TopologicalSpace X] [PseudoMetricSpace W]
    (F : {r : ℝ // 0 ≤ r} → A → X → W) (E : ℝ → X → ℝ) (x₀ : X)
    (hE : Continuous (fun p : ℝ × X => E p.1 p.2))
    (hzero : ∀ r, E r x₀ = 0)
    (hbound : ∀ r a x, dist (F r a x₀) (F r a x) ≤ E r.val x)
    (htail : Tendsto (fun p : ℝ × X => E p.1 p.2)
      (atTop ×ˢ 𝓝 x₀) (𝓝 0)) :
    EquicontinuousAt (fun p : {r : ℝ // 0 ≤ r} × A => F p.1 p.2) x₀ := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  filter_upwards [uniform_nonnegative_parameter_of_joint_limit E x₀ hE hzero htail ε hε]
    with x hx
  intro p
  exact (hbound p.1 p.2 x).trans_lt (hx p.1.val p.1.property)

end PolycyclicRecognition

end OAI
