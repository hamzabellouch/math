import OAI.GroupTheory.PolycyclicRecognition.Analysis.DeterministicProbabilityComparison
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TranslatedCellDomination

namespace OAI

/-! # Transferring affine approximation through a dominated sampling law -/

namespace PolycyclicRecognition
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Ordinary affine approximation and suffix concentration give the same
approximation for a changed sampling law dominated by the independent
starting-point and suffix distribution. -/
theorem dominated_profile_concentration
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ ν : ℕ → ProbabilityMeasure X) (ξ : ℕ → Measure X)
    (ψ : ℕ → X → X) (m : ℕ → X → X → X)
    (f : ℕ → X → Y) (a : ℕ → Y)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hmeas : ∀ n ε, MeasurableSet {x | ε ≤ dist (f n x) (a n)})
    (hdom : ∀ᶠ n in atTop, ∀ S : Set X, MeasurableSet S →
      ξ n (ψ n ⁻¹' S) ≤ K * (μ n : Measure X).prod (ν n : Measure X)
        {p | m n p.1 p.2 ∈ S})
    (hordinary : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (f n x) (a n)}) atTop (𝓝 0))
    (hsuffix : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | ε ≤ dist (f n (m n p.1 p.2)) (f n p.1)}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => ξ n {x | ε ≤ dist (f n (ψ n x)) (a n)}) atTop (𝓝 0) := by
  have ho : ∀ η : ℝ, 0 < η → Tendsto (fun n =>
      (μ n : Measure X).prod (ν n : Measure X)
        {p | η ≤ dist (f n p.1) (a n)}) atTop (𝓝 0) := by
    intro η hη
    have he n : {p : X × X | η ≤ dist (f n p.1) (a n)} =
        {x | η ≤ dist (f n x) (a n)} ×ˢ univ := by ext p; simp
    simpa only [he, Measure.prod_prod, measure_univ, mul_one] using hordinary η hη
  have hp := bad_distance_triangle_tendsto_zero
    (fun n => (μ n : Measure X).prod (ν n : Measure X))
    (fun n p => f n (m n p.1 p.2)) (fun n p => f n p.1) (fun n _ => a n)
    hsuffix ho ε hε
  have hlim := ENNReal.Tendsto.const_mul hp (Or.inr hK)
  simp only [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hdom] with n hn
  exact hn _ (hmeas n ε)

end PolycyclicRecognition

end OAI
