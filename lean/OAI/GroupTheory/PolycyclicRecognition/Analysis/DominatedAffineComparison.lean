import OAI.GroupTheory.PolycyclicRecognition.Analysis.ExactProfileTransport
import OAI.GroupTheory.PolycyclicRecognition.Analysis.DominatedProfileConcentration

namespace OAI

/-! # Affine comparison under the changed-center sampling law -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The proved density domination and suffix concentration transport the
target affine approximant to the source law, where the exact chart identity
compares the two deterministic approximants. -/
theorem deterministic_distance_tendsto_zero_of_dominated_transport
    {X Y Z : Type*} [MeasurableSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (ξ μ ν : ℕ → ProbabilityMeasure X) (a : ℕ → Y) (b : ℕ → Z)
    (f : ℕ → X → Y) (g : ℕ → X → Z) (ψ : ℕ → X → X)
    (m : ℕ → X → X → X) (H : ℕ → Z → Y)
    {K : ℝ} (hK : 0 < K)
    (hH : ∀ n u v, dist (H n u) (H n v) ≤ K * dist u v)
    (hmatch : ∀ᶠ n in atTop, ∀ x, f n x = H n (g n (ψ n x)))
    {D : ℝ≥0∞} (hD : D ≠ ∞)
    (hmeas : ∀ n ε, MeasurableSet {x | ε ≤ dist (g n x) (b n)})
    (hdom : ∀ᶠ n in atTop, ∀ S : Set X, MeasurableSet S →
      (ξ n : Measure X) (ψ n ⁻¹' S) ≤ D * (μ n : Measure X).prod (ν n : Measure X)
        {p | m n p.1 p.2 ∈ S})
    (hsource : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (ξ n : Measure X) {x | ε ≤ dist (a n) (f n x)}) atTop (𝓝 0))
    (hordinary : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (g n x) (b n)}) atTop (𝓝 0))
    (hsuffix : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (g n (m n p.1 p.2)) (g n p.1)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (H n (b n))) atTop (𝓝 0) := by
  have hsource' : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (ξ n : Measure X) {x | ε ≤ dist (a n) (H n (g n (ψ n x)))}) atTop (𝓝 0) := by
    intro ε hε
    apply (hsource ε hε).congr'
    filter_upwards [hmatch] with n hn
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, hn x]
  apply deterministic_distance_tendsto_zero_of_exact_transport ξ a b
    (fun n x => H n (g n (ψ n x)))
    (fun n x => g n (ψ n x)) H hK hH (fun _ _ => rfl) hsource'
  intro ε hε
  exact dominated_profile_concentration μ ν (fun n => (ξ n : Measure X)) ψ m g b
    hD hmeas hdom hordinary hsuffix hε

end PolycyclicRecognition

end

end OAI
