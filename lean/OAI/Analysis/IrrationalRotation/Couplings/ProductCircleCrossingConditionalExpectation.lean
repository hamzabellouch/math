import OAI.Analysis.IrrationalRotation.Couplings.ProductCrossingConditionalExpectation
import OAI.Analysis.IrrationalRotation.Product.ProductCircleConditioning

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Invariant233.OrderedProductCoupling
open CouplingMarginalBounds

theorem crossing_event_ae_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    {ω : Sample | leftEndpoint ω i < u i ∧ u i ≤ rightEndpoint ω i} =ᵐ[law P]
      {ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i ∧
        u i ≤ realEndpoint (circleRightEndpoint ω) i} := by
  filter_upwards [ae_real_circle_endpoints P] with ω hω
  rw [hω.1, hω.2]

theorem right_crossing_condExp_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    (law P)[{ω : Sample | leftEndpoint ω i < u i ∧ u i ≤ rightEndpoint ω i}.indicator
      (fun _ => (1 : ℝ)) | (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]
      =ᵐ[law P]
    (law P)[{ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i ∧
      u i ≤ realEndpoint (circleRightEndpoint ω) i}.indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint] := by
  exact (left_condExp_eq_circle P _).trans
    (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (crossing_event_ae_eq_circle P u i)))

theorem left_crossing_condExp_eq_circle (P : Parameters) (u : ℕ → ℝ) (i : ℕ) :
    (law P)[{ω : Sample | leftEndpoint ω i < u i ∧ u i ≤ rightEndpoint ω i}.indicator
      (fun _ => (1 : ℝ)) | (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]
      =ᵐ[law P]
    (law P)[{ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u i ∧
      u i ≤ realEndpoint (circleRightEndpoint ω) i}.indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint] := by
  exact (right_condExp_eq_circle P _).trans
    (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (crossing_event_ae_eq_circle P u i)))

theorem circle_crossing_condExp_lower_countable {K : Type*} [Countable K]
    (P : Parameters) (u : K → ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (k : K) (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u k i → u k i ≤ 1 - w →
      (realEndpoint (circleLeftEndpoint ω) i < u k i →
        rho (P.κ i) (P.m i) w / 10 ≤
          ((law P)[{ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u k i ∧
            u k i ≤ realEndpoint (circleRightEndpoint ω) i}.indicator (fun _ => (1 : ℝ)) |
            (inferInstance : MeasurableSpace ProductModel.Base).comap circleLeftEndpoint]) ω) ∧
      (u k i ≤ realEndpoint (circleRightEndpoint ω) i →
        rho (P.κ i) (P.m i) w / 10 ≤
          ((law P)[{ω : Sample | realEndpoint (circleLeftEndpoint ω) i < u k i ∧
            u k i ≤ realEndpoint (circleRightEndpoint ω) i}.indicator (fun _ => (1 : ℝ)) |
            (inferInstance : MeasurableSpace ProductModel.Base).comap circleRightEndpoint]) ω) := by
  have hr := ae_all_iff.mpr (fun k =>
    ae_all_iff.mpr (right_crossing_condExp_eq_circle P (u k)))
  have hl := ae_all_iff.mpr (fun k =>
    ae_all_iff.mpr (left_crossing_condExp_eq_circle P (u k)))
  filter_upwards [crossing_condExp_lower_countable P u, ae_real_circle_endpoints P,
    hr, hl] with ω hraw hrep hright hleft
  intro k i w hw hwu huw
  constructor
  · intro hxu
    rw [← hright k i]
    apply (hraw k i w hw hwu huw).1
    simpa only [hrep.1] using hxu
  · intro huy
    rw [← hleft k i]
    apply (hraw k i w hw hwu huw).2
    simpa only [hrep.2] using huy

end Invariant233.OrderedProductCoupling

end

end OAI
