import OAI.Geometry.RCD.Sobolev.PoissonHarmonicCompactnessInput

namespace OAI

/-! # Preserve one joint limit when extracting coefficient subsequences -/

open Set Metric MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- All value moments and radial gradient tests retain the SAME model
under any later strictly increasing subsequence. -/
theorem PoissonHarmonicLimit.subsequence {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    {S : ℝ} {p : ℕ → X} {r : ℕ → ℝ}
    {u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic}
    {V : ℕ → X → Euclidean n} {w f : ℕ → SobolevSpace (hausdorff n X) hX.quadratic}
    {model : EuclideanHarmonicModel n S} (h : PoissonHarmonicLimit hX S p r u V w f model)
    (t : ℕ → ℕ) (ht : StrictMono t) :
    PoissonHarmonicLimit hX S (p ∘ t) (r ∘ t) (u ∘ t) (V ∘ t) (w ∘ t) (f ∘ t) model := by
  constructor
  · intro ρ hρ hρS i j
    exact (h.moments ρ hρ hρS i j).comp ht.tendsto_atTop
  · intro ψ hψ
    obtain ⟨hD, hW, hO, hU⟩ := h.tests ψ hψ
    exact ⟨hD.comp ht.tendsto_atTop, hW.comp ht.tendsto_atTop,
      hO.comp ht.tendsto_atTop, fun j => (hU j).comp ht.tendsto_atTop⟩

end RegularPointCoordinates

end

end OAI
