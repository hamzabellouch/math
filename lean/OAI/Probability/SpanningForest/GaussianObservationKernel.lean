import OAI.Probability.SpanningForest.FiniteProductDensity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem336.GaussianObservation

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

def endpointKernel (v : ℝ≥0) (ξ : α → ι → ℝ) : Kernel α (ι → ℝ) :=
  (Kernel.const α (Measure.pi (fun _ : ι => gaussianReal 0 v))).withDensity
    (fun a y => ENNReal.ofReal (Real.exp (∑ i, (y i - (v : ℝ) / 2) * ξ a i)))

theorem measurable_endpoint_likelihood (v : ℝ≥0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i)) :
    Measurable (Function.uncurry
      (fun (a : α) (y : ι → ℝ) =>
        ENNReal.ofReal (Real.exp (∑ i, (y i - (v : ℝ) / 2) * ξ a i)))) := by
  change Measurable (fun q : α × (ι → ℝ) =>
    ENNReal.ofReal (Real.exp (∑ i, (q.2 i - (v : ℝ) / 2) * ξ q.1 i)))
  fun_prop

theorem endpointKernel_apply (v : ℝ≥0) (hv : v ≠ 0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1) (a : α) :
    endpointKernel v ξ a = Measure.pi (fun i => gaussianReal ((v : ℝ) * ξ a i) v) := by
  rw [endpointKernel, Kernel.withDensity_apply _ (measurable_endpoint_likelihood v ξ hξ),
    Kernel.const_apply]
  exact (gaussian_pi_binary_shift_withDensity v hv (ξ a) (hbinary a)).symm

theorem endpointKernel_markov (v : ℝ≥0) (hv : v ≠ 0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1) : IsMarkovKernel (endpointKernel v ξ) := by
  constructor
  intro a
  rw [endpointKernel_apply v hv ξ hξ hbinary a]
  infer_instance

theorem endpointKernel_apply_all (v : ℝ≥0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1) (a : α) :
    endpointKernel v ξ a = Measure.pi (fun i => gaussianReal ((v : ℝ) * ξ a i) v) := by
  rw [endpointKernel, Kernel.withDensity_apply _ (measurable_endpoint_likelihood v ξ hξ),
    Kernel.const_apply]
  exact (gaussian_pi_binary_shift_withDensity_all v (ξ a) (hbinary a)).symm

theorem endpointKernel_markov_all (v : ℝ≥0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1) : IsMarkovKernel (endpointKernel v ξ) := by
  constructor
  intro a
  rw [endpointKernel_apply_all v ξ hξ hbinary a]
  infer_instance

theorem centered_gaussian_pi_map_shift (v : ℝ≥0) (z : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).map (fun y i => z i + y i) =
      Measure.pi (fun i => gaussianReal (z i) v) := by
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  congr 1
  funext i
  simpa only [zero_add] using (gaussianReal_map_const_add (μ := 0) (v := v) (z i))

theorem map_prod_endpoint_eq_compProd (v : ℝ≥0) (hv : v ≠ 0)
    (ξ : α → ι → ℝ) (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1)
    (π : Measure α) [SFinite π] :
    (π.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))).map
      (fun q => (q.1, fun i => (v : ℝ) * ξ q.1 i + q.2 i)) =
        π ⊗ₘ endpointKernel v ξ := by
  let := endpointKernel_markov v hv ξ hξ hbinary
  have hmap : Measurable (fun q : α × (ι → ℝ) =>
      (q.1, fun i => (v : ℝ) * ξ q.1 i + q.2 i)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hmap hs, Measure.prod_apply (hs.preimage hmap),
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro a
  rw [endpointKernel_apply v hv ξ hξ hbinary a,
    ← centered_gaussian_pi_map_shift v (fun i => (v : ℝ) * ξ a i),
    Measure.map_apply (by fun_prop) (hs.preimage measurable_prodMk_left)]
  rfl

theorem hasLaw_independent_gaussian_observation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Measure α) [IsProbabilityMeasure π]
    (v : ℝ≥0) (hv : v ≠ 0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1)
    (X : Ω → α) (B : Ω → ι → ℝ) (hX : HasLaw X π P)
    (hB : HasLaw B (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hIndep : IndepFun X B P) :
    HasLaw (fun ω => (X ω, fun i => (v : ℝ) * ξ (X ω) i + B ω i))
      (π ⊗ₘ endpointKernel v ξ) P := by
  have hpair := hIndep.hasLaw_prod hX hB
  have hmap : HasLaw
      (fun q : α × (ι → ℝ) => (q.1, fun i => (v : ℝ) * ξ q.1 i + q.2 i))
      (π ⊗ₘ endpointKernel v ξ)
      (π.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))) :=
    ⟨by fun_prop, map_prod_endpoint_eq_compProd v hv ξ hξ hbinary π⟩
  exact hmap.fun_comp hpair

theorem map_prod_endpoint_eq_compProd_all (v : ℝ≥0)
    (ξ : α → ι → ℝ) (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1)
    (π : Measure α) [SFinite π] :
    (π.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))).map
      (fun q => (q.1, fun i => (v : ℝ) * ξ q.1 i + q.2 i)) =
        π ⊗ₘ endpointKernel v ξ := by
  let := endpointKernel_markov_all v ξ hξ hbinary
  have hmap : Measurable (fun q : α × (ι → ℝ) =>
      (q.1, fun i => (v : ℝ) * ξ q.1 i + q.2 i)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hmap hs, Measure.prod_apply (hs.preimage hmap),
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro a
  rw [endpointKernel_apply_all v ξ hξ hbinary a,
    ← centered_gaussian_pi_map_shift v (fun i => (v : ℝ) * ξ a i),
    Measure.map_apply (by fun_prop) (hs.preimage measurable_prodMk_left)]
  rfl

theorem hasLaw_independent_gaussian_observation_all {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Measure α) [IsProbabilityMeasure π]
    (v : ℝ≥0) (ξ : α → ι → ℝ)
    (hξ : ∀ i, Measurable (fun a => ξ a i))
    (hbinary : ∀ a i, ξ a i = 0 ∨ ξ a i = 1)
    (X : Ω → α) (B : Ω → ι → ℝ) (hX : HasLaw X π P)
    (hB : HasLaw B (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hIndep : IndepFun X B P) :
    HasLaw (fun ω => (X ω, fun i => (v : ℝ) * ξ (X ω) i + B ω i))
      (π ⊗ₘ endpointKernel v ξ) P := by
  have hpair := hIndep.hasLaw_prod hX hB
  have hmap : HasLaw
      (fun q : α × (ι → ℝ) => (q.1, fun i => (v : ℝ) * ξ q.1 i + q.2 i))
      (π ⊗ₘ endpointKernel v ξ)
      (π.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))) :=
    ⟨by fun_prop, map_prod_endpoint_eq_compProd_all v ξ hξ hbinary π⟩
  exact hmap.fun_comp hpair

end Problem336.GaussianObservation

end

end OAI
