import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli

namespace OAI

/-! # Equicontinuity from a vanishing error at large chart scales -/

namespace PolycyclicRecognition

open Filter Set
open scoped Topology

variable {X W A : Type*} [TopologicalSpace X] [PseudoMetricSpace W]

/-- A bound vanishing jointly as the scale grows and the point approaches
`x₀`, together with equicontinuity at each fixed scale, controls the entire
family. The auxiliary index allows all random chart samples at each scale. -/
theorem equicontinuousAt_of_joint_error_tendsto
    (F : ℕ → A → X → W) (E : ℕ → X → ℝ) (x₀ : X)
    (hhead : ∀ n, EquicontinuousAt (F n) x₀)
    (hbound : ∀ n a x, dist (F n a x₀) (F n a x) ≤ E n x)
    (htail : Tendsto (fun p : ℕ × X => E p.1 p.2)
      (atTop ×ˢ 𝓝 x₀) (𝓝 0)) :
    EquicontinuousAt (fun p : ℕ × A => F p.1 p.2) x₀ := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have he := htail.eventually (eventually_lt_nhds hε)
  obtain ⟨s, hs, t, ht, hst⟩ := mem_prod_iff.mp he
  obtain ⟨N, hN⟩ := eventually_atTop.mp hs
  have hf : ∀ᶠ x in 𝓝 x₀, ∀ i : Fin N, ∀ a, dist (F i a x₀) (F i a x) < ε :=
    eventually_all.mpr (fun i =>
      (Metric.equicontinuousAt_iff_right.mp (hhead i)) ε hε)
  filter_upwards [ht, hf] with x hx hfx
  intro p
  by_cases hp : p.1 < N
  · exact hfx ⟨p.1, hp⟩ p.2
  · exact (hbound p.1 p.2 x).trans_lt (hst (show (p.1, x) ∈ s ×ˢ t from ⟨hN p.1 (Nat.le_of_not_gt hp), hx⟩))

/-- The fixed-scale hypothesis can itself be supplied by the continuous
metric error bound; no common modulus at small scales is needed. -/
theorem equicontinuousAt_of_continuous_joint_error
    (F : ℕ → A → X → W) (E : ℕ → X → ℝ) (x₀ : X)
    (hE : ∀ n, ContinuousAt (E n) x₀) (hzero : ∀ n, E n x₀ = 0)
    (hbound : ∀ n a x, dist (F n a x₀) (F n a x) ≤ E n x)
    (htail : Tendsto (fun p : ℕ × X => E p.1 p.2)
      (atTop ×ˢ 𝓝 x₀) (𝓝 0)) :
    EquicontinuousAt (fun p : ℕ × A => F p.1 p.2) x₀ := by
  apply equicontinuousAt_of_joint_error_tendsto F E x₀ _ hbound htail
  intro n
  apply Metric.equicontinuousAt_of_continuity_modulus (E n)
  · simpa only [hzero n] using (hE n).tendsto
  · exact Eventually.of_forall (fun x a => hbound n a x)

end PolycyclicRecognition

end OAI
