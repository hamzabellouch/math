import OAI.Probability.FreeIsing.Conditioning.ObservationCopyStationarity
import OAI.Probability.FreeIsing.Martingales.InnovationMartingale

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem observations_ae_eq_of_common_innovation_and_field_zero
    {O : Type*} [MeasurableSpace O] {mu : Measure O}
    {h h' : ℝ≥0 → O → ℝ} {X Y W : ℕ → O → ℝ}
    (hc : ∀ᵐ p ∂mu, Continuous (fun t => h t p))
    (hc' : ∀ᵐ p ∂mu, Continuous (fun t => h' t p))
    (hInt : ∀ t, Integrable (fun p => (h t p - h' t p) ^ 2) mu)
    (hzero : ∀ t, (∫ p, (h t p - h' t p) ^ 2 ∂mu) = 0)
    (hX : ∀ n, ∀ᵐ p ∂mu,
      X n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h t p)) n p)
    (hY : ∀ n, ∀ᵐ p ∂mu,
      Y n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h' t p)) n p) :
    ∀ n, X n =ᵐ[mu] Y n := by
  have hfield : (fun p t => h t p) =ᵐ[mu] (fun p t => h' t p) :=
    ae_eq_of_continuous_of_integral_sq_sub_eq_zero hc hc' hInt hzero
  intro n
  filter_upwards [hfield, hX n, hY n] with p hp hx hy
  rw [hx, hy]
  congr 1
  unfold nnrealTimePrimitive
  apply intervalIntegral.integral_congr
  intro t _
  exact congrArg Real.tanh (congrFun hp t.toNNReal)

theorem observations_ae_eq_of_common_innovation_and_measurable_fields
    {O : Type*} [MeasurableSpace O] {mu : Measure O} [SFinite mu]
    {h h' : ℝ≥0 → O → ℝ} {X Y W : ℕ → O → ℝ}
    (hm : Measurable (fun q : ℝ × O => Real.tanh (h q.1.toNNReal q.2)))
    (hm' : Measurable (fun q : ℝ × O => Real.tanh (h' q.1.toNNReal q.2)))
    (heq : ∀ t, h t =ᵐ[mu] h' t)
    (hX : ∀ n, ∀ᵐ p ∂mu,
      X n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h t p)) n p)
    (hY : ∀ n, ∀ᵐ p ∂mu,
      Y n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h' t p)) n p) :
    ∀ n, X n =ᵐ[mu] Y n := by
  have htime : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ p ∂mu,
      Real.tanh (h t.toNNReal p) = Real.tanh (h' t.toNNReal p) := by
    apply Filter.Eventually.of_forall
    intro t
    filter_upwards [heq t.toNNReal] with p hp
    rw [hp]
  have hsample : ∀ᵐ p ∂mu, ∀ᵐ t ∂(volume : Measure ℝ),
      Real.tanh (h t.toNNReal p) = Real.tanh (h' t.toNNReal p) :=
    (Measure.ae_ae_comm (μ := (volume : Measure ℝ)) (ν := mu)
      (p := fun t p => Real.tanh (h t.toNNReal p) = Real.tanh (h' t.toNNReal p))
      (measurableSet_eq_fun hm hm')).1 htime
  intro n
  filter_upwards [hsample, hX n, hY n] with p hp hx hy
  rw [hx, hy]
  congr 1
  unfold nnrealTimePrimitive
  apply intervalIntegral.integral_congr_ae
  exact hp.mono (fun _ ht _ => ht)

theorem observations_ae_eq_of_common_innovation_and_measurable_field_zero
    {O : Type*} [MeasurableSpace O] {mu : Measure O} [SFinite mu]
    {h h' : ℝ≥0 → O → ℝ} {X Y W : ℕ → O → ℝ}
    (hm : Measurable (fun q : ℝ × O => Real.tanh (h q.1.toNNReal q.2)))
    (hm' : Measurable (fun q : ℝ × O => Real.tanh (h' q.1.toNNReal q.2)))
    (hInt : ∀ t, Integrable (fun p => (h t p - h' t p) ^ 2) mu)
    (hzero : ∀ t, (∫ p, (h t p - h' t p) ^ 2 ∂mu) = 0)
    (hX : ∀ n, ∀ᵐ p ∂mu,
      X n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h t p)) n p)
    (hY : ∀ n, ∀ᵐ p ∂mu,
      Y n p = W n p + nnrealTimePrimitive (fun t p => Real.tanh (h' t p)) n p) :
    ∀ n, X n =ᵐ[mu] Y n := by
  apply observations_ae_eq_of_common_innovation_and_measurable_fields hm hm' _ hX hY
  exact fun t => ae_eq_of_integral_sq_sub_eq_zero (hInt t) (hzero t)

theorem isFactorOfIID_of_joint_innovation_field_zero
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (rho : Measure ((TreeVertex d → A) × (TreeVertex d → ℕ → ℝ)))
    [IsProbabilityMeasure rho] (o : TreeVertex d)
    (hfirst : rho.fst = Measure.infinitePi (fun _ : TreeVertex d => nu))
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray p.2) rho))
    (hjoint : ∀ g : TreeAut d, rho.map (Prod.map (relabel g) (relabel g)) = rho)
    (h h' : ℝ≥0 →
      ((TreeVertex d → A) × ((TreeVertex d → ℕ → ℝ) × (TreeVertex d → ℕ → ℝ))) → ℝ)
    (W : ℕ → (TreeVertex d → A) → ℝ)
    (hc : ∀ᵐ p ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel),
      Continuous (fun t => h t p))
    (hc' : ∀ᵐ p ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel),
      Continuous (fun t => h' t p))
    (hInt : ∀ t, Integrable (fun p => (h t p - h' t p) ^ 2)
      (rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)))
    (hzero : ∀ t, (∫ p, (h t p - h' t p) ^ 2
      ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)) = 0)
    (hX : ∀ n, ∀ᵐ p ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel),
      p.2.1 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (h t p)) n p)
    (hY : ∀ n, ∀ᵐ p ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel),
      p.2.2 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (h' t p)) n p) :
    IsFactorOfIID d theta := by
  apply ObservationCopyStationarity.isFactorOfIID_of_joint_observation_reference_collapse
    nu rho o hfirst hLaw hjoint
  exact observations_ae_eq_of_common_innovation_and_field_zero hc hc' hInt hzero hX hY

theorem isFactorOfIID_of_joint_innovation_measurable_field_zero
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    [StandardBorelSpace A] [Nonempty A]
    (nu : Measure A) [IsProbabilityMeasure nu]
    (rho : Measure ((TreeVertex d → A) × (TreeVertex d → ℕ → ℝ)))
    [IsProbabilityMeasure rho] (o : TreeVertex d)
    (hfirst : rho.fst = Measure.infinitePi (fun _ : TreeVertex d => nu))
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (fun p => SpinRecovery.decodeArray p.2) rho))
    (hjoint : ∀ g : TreeAut d, rho.map (Prod.map (relabel g) (relabel g)) = rho)
    (h h' : ℝ≥0 →
      ((TreeVertex d → A) × ((TreeVertex d → ℕ → ℝ) × (TreeVertex d → ℕ → ℝ))) → ℝ)
    (W : ℕ → (TreeVertex d → A) → ℝ)
    (hm : Measurable (Function.uncurry (fun (t : ℝ) p => Real.tanh (h t.toNNReal p))))
    (hm' : Measurable (Function.uncurry (fun (t : ℝ) p => Real.tanh (h' t.toNNReal p))))
    (hInt : ∀ t, Integrable (fun p => (h t p - h' t p) ^ 2)
      (rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)))
    (hzero : ∀ t, (∫ p, (h t p - h' t p) ^ 2
      ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel)) = 0)
    (hX : ∀ n, ∀ᵐ p ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel),
      p.2.1 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (h t p)) n p)
    (hY : ∀ n, ∀ᵐ p ∂rho.fst ⊗ₘ (rho.condKernel ×ₖ rho.condKernel),
      p.2.2 o n = W n p.1 + nnrealTimePrimitive (fun t p => Real.tanh (h' t p)) n p) :
    IsFactorOfIID d theta := by
  apply ObservationCopyStationarity.isFactorOfIID_of_joint_observation_reference_collapse
    nu rho o hfirst hLaw hjoint
  exact observations_ae_eq_of_common_innovation_and_measurable_field_zero
    hm hm' hInt hzero hX hY

end Problem367

end

end OAI
