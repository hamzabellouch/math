import OAI.Probability.DilutedSpin.ReservoirTrees

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i,Fintype (A i)] {p L N : ℕ} [NeZero N]

lemma perturbedMean_score_rate (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j,0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hD : 0≤D) (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) (u v w : ℝ≥0) (hvw : v≤w) :
    |perturbedMean (N := N) μ ξ ν theta field Q m ψ u w-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ u v|≤D*((w:ℝ)-v) := by
  have h := twoPoissonMean_rate_add_right u v (w-v)
    (countedMean_bound (N := N) μ ξ ν theta field Q m hm ψ hθ hh hψ) hD
    (countedMean_mark_step μ ξ ν theta field hθm hhm Q m hm ψ hθ hh hψ)
  rw [add_tsub_cancel_of_le hvw,NNReal.coe_sub hvw] at h
  simpa only [perturbedMean,add_sub_add_left_eq_sub] using h

end DilutedSpinGlass.SizeCoupling

end

end OAI
