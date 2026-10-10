import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def vertexSampler {d : ℕ} {α β : Type*} (f : α → β)
    (x : TreeVertex d → α) : TreeVertex d → β := fun v => f (x v)

@[simp] theorem vertexSampler_relabel {d : ℕ} {α β : Type*}
    (f : α → β) (g : TreeAut d) (x : TreeVertex d → α) :
    vertexSampler f (relabel g x) = relabel g (vertexSampler f x) := rfl

theorem measurable_vertexSampler {d : ℕ} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) : Measurable (vertexSampler (d := d) f) := by
  exact Measurable.of_eval fun vertex => hf.comp (measurable_pi_apply vertex)

theorem map_vertexSampler_labelMeasure {d : ℕ} {α : Type*}
    [MeasurableSpace α] {f : ℝ → α} (hf : Measurable f) :
    Measure.map (vertexSampler (d := d) f) (labelMeasure d) =
      Measure.infinitePi (fun _ : TreeVertex d => Measure.map f uniform01) := by
  exact Measure.infinitePi_map_pi (fun _ => uniform01) (fun _ => hf)

theorem isFactorOfIID_of_product_sampler {d : ℕ} {theta : ℝ} {α : Type*}
    [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : ℝ → α) (hf : Measurable f) (hf_law : Measure.map f uniform01 = ν)
    (H : (TreeVertex d → α) → (TreeVertex d → IsingSpin))
    (hH : Measurable H)
    (hLaw : HasFreeIsingLaw theta
      (Measure.map H (Measure.infinitePi (fun _ : TreeVertex d => ν))))
    (hEquiv : ∀ g : TreeAut d,
      ∀ᵐ W ∂Measure.infinitePi (fun _ : TreeVertex d => ν),
        H (relabel g W) = relabel g (H W)) :
    IsFactorOfIID d theta := by
  have hs := measurable_vertexSampler (d := d) hf
  have hslaw : Measure.map (vertexSampler (d := d) f) (labelMeasure d) =
      Measure.infinitePi (fun _ : TreeVertex d => ν) := by
    rw [map_vertexSampler_labelMeasure hf, hf_law]
  refine ⟨H ∘ vertexSampler f, hH.comp hs, ?_, ?_⟩
  · rw [← Measure.map_map hH hs, hslaw]
    exact hLaw
  · intro g
    have h : ∀ᵐ W ∂Measure.map (vertexSampler (d := d) f) (labelMeasure d),
        H (relabel g W) = relabel g (H W) := by
      rw [hslaw]
      exact hEquiv g
    filter_upwards [ae_of_ae_map hs.aemeasurable h] with U hU
    simpa only [Function.comp_apply, vertexSampler_relabel] using hU

end Problem367

end

end OAI
