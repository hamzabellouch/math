import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalThresholds
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace Invariant233.OrderedProductCoupling
open CouplingMarginalBounds

theorem right_crossing_condExp_eq (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ i : ℕ,
      ((law P)[{ω : Sample | leftEndpoint ω i < u i ∧ u i ≤ rightEndpoint ω i}.indicator
        (fun _ => (1 : ℝ)) | (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]) ω =
      {ω : Sample | leftEndpoint ω i < u i}.indicator
        ((law P)[{ω : Sample | u i ≤ rightEndpoint ω i}.indicator (fun _ => (1 : ℝ)) |
          (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]) ω := by
  apply ae_all_iff.mpr
  intro i
  have htop : MeasurableSet {ω : Sample | u i ≤ rightEndpoint ω i} :=
    measurableSet_le measurable_const ((measurable_pi_apply i).comp rightEndpoint_measurable)
  have helig : MeasurableSet[(inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]
      {ω : Sample | leftEndpoint ω i < u i} := by
    exact ⟨{x : Endpoint | x i < u i},
      measurableSet_lt (measurable_pi_apply i) measurable_const, rfl⟩
  have h := condExp_indicator (μ := law P)
    ((integrable_const (1 : ℝ)).indicator htop) helig
  filter_upwards [h] with ω hω
  simpa only [Set.indicator_indicator, Set.ofPred_and] using hω

theorem left_crossing_condExp_eq (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ i : ℕ,
      ((law P)[{ω : Sample | leftEndpoint ω i < u i ∧ u i ≤ rightEndpoint ω i}.indicator
        (fun _ => (1 : ℝ)) | (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]) ω =
      {ω : Sample | u i ≤ rightEndpoint ω i}.indicator
        ((law P)[{ω : Sample | leftEndpoint ω i < u i}.indicator (fun _ => (1 : ℝ)) |
          (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]) ω := by
  apply ae_all_iff.mpr
  intro i
  have hbottom : MeasurableSet {ω : Sample | leftEndpoint ω i < u i} :=
    measurableSet_lt ((measurable_pi_apply i).comp leftEndpoint_measurable) measurable_const
  have helig : MeasurableSet[(inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]
      {ω : Sample | u i ≤ rightEndpoint ω i} := by
    exact ⟨{y : Endpoint | u i ≤ y i},
      measurableSet_le measurable_const (measurable_pi_apply i), rfl⟩
  have h := condExp_indicator (μ := law P)
    ((integrable_const (1 : ℝ)).indicator hbottom) helig
  filter_upwards [h] with ω hω
  simpa only [Set.indicator_indicator, Set.ofPred_and, Set.inter_comm] using hω

theorem right_crossing_condExp_lower (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      leftEndpoint ω i < u i →
      rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | leftEndpoint ω i < u i ∧ u i ≤ rightEndpoint ω i}.indicator
          (fun _ => (1 : ℝ)) | (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]) ω := by
  filter_upwards [right_crossing_condExp_eq P u,
    right_threshold_condExp_lower_all_coordinates P u] with ω heq hbound
  intro i w hw hwu huw hxu
  rw [heq i, Set.indicator_of_mem (show ω ∈ {ω : Sample | leftEndpoint ω i < u i} from hxu)]
  exact hbound i w hw hwu huw hxu

theorem left_crossing_condExp_lower (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      u i ≤ rightEndpoint ω i →
      rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | leftEndpoint ω i < u i ∧ u i ≤ rightEndpoint ω i}.indicator
          (fun _ => (1 : ℝ)) | (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]) ω := by
  filter_upwards [left_crossing_condExp_eq P u,
    left_threshold_condExp_lower_all_coordinates P u] with ω heq hbound
  intro i w hw hwu huw huy
  rw [heq i, Set.indicator_of_mem (show ω ∈ {ω : Sample | u i ≤ rightEndpoint ω i} from huy)]
  exact hbound i w hw hwu huw huy

theorem crossing_condExp_lower_countable {K : Type*} [Countable K]
    (P : Parameters) (u : K → ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (k : K) (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u k i → u k i ≤ 1 - w →
      (leftEndpoint ω i < u k i →
        rho (P.κ i) (P.m i) w / 10 ≤
          ((law P)[{ω : Sample | leftEndpoint ω i < u k i ∧ u k i ≤ rightEndpoint ω i}.indicator
            (fun _ => (1 : ℝ)) | (inferInstance : MeasurableSpace Endpoint).comap leftEndpoint]) ω) ∧
      (u k i ≤ rightEndpoint ω i →
        rho (P.κ i) (P.m i) w / 10 ≤
          ((law P)[{ω : Sample | leftEndpoint ω i < u k i ∧ u k i ≤ rightEndpoint ω i}.indicator
            (fun _ => (1 : ℝ)) | (inferInstance : MeasurableSpace Endpoint).comap rightEndpoint]) ω) := by
  apply ae_all_iff.mpr
  intro k
  filter_upwards [right_crossing_condExp_lower P (u k),
    left_crossing_condExp_lower P (u k)] with ω hright hleft
  intro i w hw hwu huw
  exact ⟨hright i w hw hwu huw, hleft i w hw hwu huw⟩

end Invariant233.OrderedProductCoupling

end

end OAI
