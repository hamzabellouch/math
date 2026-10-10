import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalCrossing

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace Invariant233.OrderedProductCoupling
open CouplingMarginalBounds

theorem right_threshold_condExp_lower_all_coordinates (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      leftEndpoint ω i < u i →
      rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | u i ≤ rightEndpoint ω i}.indicator (fun _ => (1 : ℝ)) |
          (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]) ω := by
  apply ae_all_iff.mpr
  intro i
  have hc := ae_of_ae_map leftEndpoint_measurable.aemeasurable
    (right_condDistrib_crossing_real_lower P)
  have he := condDistrib_ae_eq_condExp (μ := law P)
    leftEndpoint_measurable rightEndpoint_measurable
    (s := {y : Endpoint | u i ≤ y i})
    (measurableSet_le measurable_const (measurable_pi_apply i))
  filter_upwards [hc, he] with ω hcross heq
  intro w hw hwu huw hxu
  have hb := hcross i w (u i) hw hwu huw hxu
  have hs : {y : Endpoint | leftEndpoint ω i < u i ∧ u i ≤ y i} =
      {y : Endpoint | u i ≤ y i} := by
    ext y
    simp only [mem_ofPred_eq, hxu, true_and]
  rw [hs] at hb
  exact heq ▸ hb

theorem left_threshold_condExp_lower_all_coordinates (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      u i ≤ rightEndpoint ω i →
      rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | leftEndpoint ω i < u i}.indicator (fun _ => (1 : ℝ)) |
          (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]) ω := by
  apply ae_all_iff.mpr
  intro i
  have hc := ae_of_ae_map rightEndpoint_measurable.aemeasurable
    (left_condDistrib_crossing_real_lower P)
  have he := condDistrib_ae_eq_condExp (μ := law P)
    rightEndpoint_measurable leftEndpoint_measurable
    (s := {x : Endpoint | x i < u i})
    (measurableSet_lt (measurable_pi_apply i) measurable_const)
  filter_upwards [hc, he] with ω hcross heq
  intro w hw hwu huw huy
  have hb := hcross i w (u i) hw hwu huw huy
  have hs : {x : Endpoint | x i < u i ∧ u i ≤ rightEndpoint ω i} =
      {x : Endpoint | x i < u i} := by
    ext x
    simp only [mem_ofPred_eq, huy, and_true]
  rw [hs] at hb
  exact heq ▸ hb

theorem threshold_condExp_lower_countable {K : Type*} [Countable K]
    (P : Parameters) (u : K → ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (k : K) (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u k i → u k i ≤ 1 - w →
      (leftEndpoint ω i < u k i →
        rho (P.κ i) (P.m i) w / 10 ≤
          ((law P)[{ω : Sample | u k i ≤ rightEndpoint ω i}.indicator (fun _ => (1 : ℝ)) |
            (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]) ω) ∧
      (u k i ≤ rightEndpoint ω i →
        rho (P.κ i) (P.m i) w / 10 ≤
          ((law P)[{ω : Sample | leftEndpoint ω i < u k i}.indicator (fun _ => (1 : ℝ)) |
            (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]) ω) := by
  apply ae_all_iff.mpr
  intro k
  filter_upwards [right_threshold_condExp_lower_all_coordinates P (u k),
    left_threshold_condExp_lower_all_coordinates P (u k)] with ω hright hleft
  intro i w hw hwu huw
  exact ⟨hright i w hw hwu huw, hleft i w hw hwu huw⟩

end Invariant233.OrderedProductCoupling

end

end OAI
