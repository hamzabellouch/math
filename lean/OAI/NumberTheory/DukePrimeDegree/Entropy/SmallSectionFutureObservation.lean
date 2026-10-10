import OAI.NumberTheory.DukePrimeDegree.Geometry.SmallPositiveSection
import OAI.NumberTheory.DukePrimeDegree.Entropy.SmallFineReturnObservation

namespace OAI

/-! # Arbitrarily low-entropy fine future observations in a chart -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

theorem exists_arbitrarily_small_fine_future_observation
    {Y : Type*} [MetricSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {T : Y → Y} (hT : Ergodic T μ) (hE : MeasurableEmbedding T)
    {A : Set Y} (hA : MeasurableSet A) (hAp : μ A ≠ 0)
    {d : ℕ} (f : Y → Fin d → ℝ) (hf : Measurable f)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ A, ∀ i, |f x i| ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Y → ℕ, Measurable Q ∧
      Summable (fun n => Real.negMulLog (μ.real {x | Q x=n})) ∧
      (∑' n, Real.negMulLog (μ.real {x | Q x=n})) < ε ∧
      ∀ᵐ x ∂μ, ∀ y, (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) →
        ∀ η : ℝ, 0 < η → ∃ k : ℕ, T^[k] x ∈ A ∧ T^[k] y ∈ A ∧
          ∀ i, |f (T^[k] y) i-f (T^[k] x) i| < η := by
  obtain ⟨δ,hδ,H⟩ := exists_small_entropy_fine_return_observation (Y := Y) (d := d) hR hε
  obtain ⟨S,hS,hSA,_,hδS,htail⟩ :=
    exists_small_positive_unbounded_return_section μ hT hE hA hAp hδ
  obtain ⟨Q,hQ,hs,he,hfine⟩ := H μ hT hE hS htail hδS f hf
    (fun x hx => hbound x (hSA hx))
  refine ⟨Q,hQ,hs,he,?_⟩
  filter_upwards [hfine] with x hx
  intro y hy η hη
  obtain ⟨k,hkx,hky,hk⟩ := hx y hy η hη
  exact ⟨k,hSA hkx,hSA hky,hk⟩

end DukePrimeDegree

end

end OAI
