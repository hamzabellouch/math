import OAI.Analysis.IrrationalRotation.Couplings.ConditionalEventBridge
import OAI.Analysis.IrrationalRotation.Couplings.ProductConditionalCrossing
import OAI.Analysis.IrrationalRotation.Couplings.FiniteConditionalAttenuation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Invariant233.OrderedProductCoupling

theorem right_thresholds_iCondIndepSet (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet (MeasurableSpace.comap leftEndpoint inferInstance)
      leftEndpoint_measurable.comap_le
      (fun i => {ω : Sample | u i ≤ rightEndpoint ω i}) (law P) := by
  apply ConditionalEventBridge.iCondIndepSet_preimage_of_condDistrib
    (law P) leftEndpoint rightEndpoint leftEndpoint_measurable rightEndpoint_measurable
    (fun i => {y : Endpoint | u i ≤ y i})
    (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  filter_upwards [right_coordinates_conditionally_independent P] with x hx
  apply (iIndepSet_iff_meas_biInter
    (fun i => measurableSet_le measurable_const (measurable_pi_apply i))).2
  intro S
  exact hx.meas_biInter (fun i _ =>
    ⟨Ici (u i), measurableSet_Ici, rfl⟩)

theorem left_thresholds_iCondIndepSet (P : Parameters) (u : ℕ → ℝ) :
    iCondIndepSet (MeasurableSpace.comap rightEndpoint inferInstance)
      rightEndpoint_measurable.comap_le
      (fun i => {ω : Sample | leftEndpoint ω i < u i}) (law P) := by
  apply ConditionalEventBridge.iCondIndepSet_preimage_of_condDistrib
    (law P) rightEndpoint leftEndpoint rightEndpoint_measurable leftEndpoint_measurable
    (fun i => {x : Endpoint | x i < u i})
    (fun i => measurableSet_lt (measurable_pi_apply i) measurable_const)
  filter_upwards [left_coordinates_conditionally_independent P] with y hy
  apply (iIndepSet_iff_meas_biInter
    (fun i => measurableSet_lt (measurable_pi_apply i) measurable_const)).2
  intro S
  exact hy.meas_biInter (fun i _ =>
    ⟨Iio (u i), measurableSet_Iio, rfl⟩)

theorem right_threshold_condExp_lower (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      leftEndpoint ω i < u i →
      CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | u i ≤ rightEndpoint ω i}.indicator
          (fun _ => (1 : ℝ)) | MeasurableSpace.comap leftEndpoint inferInstance]) ω := by
  have heq : ∀ᵐ ω ∂law P, ∀ i,
      (condDistrib rightEndpoint leftEndpoint (law P) (leftEndpoint ω)).real
        {y : Endpoint | u i ≤ y i} =
      ((law P)[{ω : Sample | u i ≤ rightEndpoint ω i}.indicator
        (fun _ => (1 : ℝ)) | MeasurableSpace.comap leftEndpoint inferInstance]) ω :=
    ae_all_iff.mpr (fun i => condDistrib_ae_eq_condExp
      leftEndpoint_measurable rightEndpoint_measurable
      (measurableSet_le measurable_const (measurable_pi_apply i)))
  have hcross := ae_of_ae_map leftEndpoint_measurable.aemeasurable
    (right_condDistrib_crossing_real_lower P)
  filter_upwards [heq, hcross] with ω heq hcross i w hw hwu huw hxu
  rw [← heq i]
  simpa only [hxu, true_and] using hcross i w (u i) hw hwu huw hxu

theorem left_threshold_condExp_lower (P : Parameters) (u : ℕ → ℝ) :
    ∀ᵐ ω ∂law P, ∀ (i : ℕ) (w : ℝ),
      (w = P.a i ∨ w = P.b i) → w ≤ u i → u i ≤ 1 - w →
      u i ≤ rightEndpoint ω i →
      CouplingMarginalBounds.rho (P.κ i) (P.m i) w / 10 ≤
        ((law P)[{ω : Sample | leftEndpoint ω i < u i}.indicator
          (fun _ => (1 : ℝ)) | MeasurableSpace.comap rightEndpoint inferInstance]) ω := by
  have heq : ∀ᵐ ω ∂law P, ∀ i,
      (condDistrib leftEndpoint rightEndpoint (law P) (rightEndpoint ω)).real
        {x : Endpoint | x i < u i} =
      ((law P)[{ω : Sample | leftEndpoint ω i < u i}.indicator
        (fun _ => (1 : ℝ)) | MeasurableSpace.comap rightEndpoint inferInstance]) ω :=
    ae_all_iff.mpr (fun i => condDistrib_ae_eq_condExp
      rightEndpoint_measurable leftEndpoint_measurable
      (measurableSet_lt (measurable_pi_apply i) measurable_const))
  have hcross := ae_of_ae_map rightEndpoint_measurable.aemeasurable
    (left_condDistrib_crossing_real_lower P)
  filter_upwards [heq, hcross] with ω heq hcross i w hw hwu huw huy
  rw [← heq i]
  simpa only [huy, and_true] using hcross i w (u i) hw hwu huw huy

theorem finite_threshold_attenuation (P : Parameters) (I : Finset ℕ)
    (u w : ℕ → ℝ)
    (hwidth : ∀ i ∈ I, w i = P.a i ∨ w i = P.b i)
    (hthreshold : ∀ i ∈ I, w i ≤ u i ∧ u i ≤ 1 - w i)
    (m ρ L : ℝ) (hρ : 0 ≤ ρ) (hL : L ≤ m * ρ)
    (hI : m / 20 ≤ (I.card : ℝ))
    (hrho : ∀ i ∈ I, ρ ≤ CouplingMarginalBounds.rho (P.κ i) (P.m i) (w i))
    (R : Sample → ℝ) (hR : ∀ᵐ ω ∂law P, R ω ≤ 1)
    (hcross : ∀ᵐ ω ∂law P, ∀ i ∈ I,
      (leftEndpoint ω i < u i ∧ u i ≤ rightEndpoint ω i) → R ω ≤ Real.exp (-L)) :
    ∃ H₁ H₂ : Set Sample, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      (∀ᵐ ω ∂law P, ((law P)[H₁.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap leftEndpoint inferInstance]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂law P, ((law P)[H₂.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap rightEndpoint inferInstance]) ω ≤ Real.exp (-L / 400)) ∧
      (∀ᵐ ω ∂law P, R ω ≤ Real.exp (-L) + H₁.indicator (fun _ => (1 : ℝ)) ω +
        H₂.indicator (fun _ => (1 : ℝ)) ω) := by
  refine CrossingAvoidance.finite_conditional_attenuation
    (MeasurableSpace.comap leftEndpoint inferInstance)
    (MeasurableSpace.comap rightEndpoint inferInstance)
    leftEndpoint_measurable.comap_le rightEndpoint_measurable.comap_le (law P)
    I u leftEndpoint rightEndpoint
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)
    (fun i => {ω : Sample | u i ≤ rightEndpoint ω i})
    (fun i => {ω : Sample | leftEndpoint ω i < u i})
    (fun i => measurableSet_le measurable_const
      ((measurable_pi_apply i).comp rightEndpoint_measurable))
    (fun i => measurableSet_lt
      ((measurable_pi_apply i).comp leftEndpoint_measurable) measurable_const)
    (right_thresholds_iCondIndepSet P u) (left_thresholds_iCondIndepSet P u)
    m ρ L hρ hL hI ?_ ?_ ?_ ?_ ?_ R hR hcross
  · exact (ae_ordered P).mono (fun _ h i _ => h i)
  · exact Filter.Eventually.of_forall (fun _ _ _ _ h => h)
  · exact Filter.Eventually.of_forall (fun _ _ _ _ h => h)
  · filter_upwards [right_threshold_condExp_lower P u] with ω hω i hi hxi
    exact (div_le_div_of_nonneg_right (hrho i hi) (by norm_num)).trans
      (hω i (w i) (hwidth i hi) (hthreshold i hi).1 (hthreshold i hi).2 hxi)
  · filter_upwards [left_threshold_condExp_lower P u] with ω hω i hi hyi
    exact (div_le_div_of_nonneg_right (hrho i hi) (by norm_num)).trans
      (hω i (w i) (hwidth i hi) (hthreshold i hi).1 (hthreshold i hi).2 hyi)

end Invariant233.OrderedProductCoupling

end

end OAI
