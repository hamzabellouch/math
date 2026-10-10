import OAI.Probability.FreeIsing.Estimates.InfinitePiPair
import OAI.Probability.FreeIsing.Estimates.UniformSampler
import OAI.Probability.FreeIsing.Factors.Transfer

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem exists_uniform01_independent_samplers
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Nonempty α] [Nonempty β] [StandardBorelSpace α] [StandardBorelSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ f : ℝ → α, ∃ g : ℝ → β,
      Measurable f ∧ Measurable g ∧
      Measure.map (fun u => (f u, g u)) uniform01 = μ.prod ν := by
  obtain ⟨ξ, hξ, hξlaw⟩ := exists_uniform01_sampler (μ.prod ν)
  exact ⟨fun u => (ξ u).1, fun u => (ξ u).2,
    measurable_fst.comp hξ, measurable_snd.comp hξ, hξlaw⟩

theorem map_independent_vertexSamplers
    {d : ℕ} {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → α} {g : ℝ → β} (hf : Measurable f) (hg : Measurable g)
    (hlaw : Measure.map (fun u => (f u, g u)) uniform01 = μ.prod ν) :
    Measure.map (fun U => (vertexSampler (d := d) f U, vertexSampler g U))
        (labelMeasure d) =
      (Measure.infinitePi (fun _ : TreeVertex d => μ)).prod
        (Measure.infinitePi (fun _ : TreeVertex d => ν)) := by
  calc
    _ = (Measure.map (vertexSampler (d := d) (fun u => (f u, g u)))
        (labelMeasure d)).map
        (fun U => (fun i => (U i).1, fun i => (U i).2)) := by
      rw [Measure.map_map (by fun_prop) (measurable_vertexSampler (hf.prodMk hg))]
      rfl
    _ = _ := by
      rw [map_vertexSampler_labelMeasure (hf.prodMk hg), hlaw]
      exact infinitePi_map_split_pairs (fun _ : TreeVertex d => μ) (fun _ => ν)

theorem map_pair_of_independent_vertexSamplers
    {d : ℕ} {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → α} {g : ℝ → β} (hf : Measurable f) (hg : Measurable g)
    (hlaw : Measure.map (fun u => (f u, g u)) uniform01 = μ.prod ν)
    {F : (TreeVertex d → α) → γ} {G : (TreeVertex d → β) → δ}
    (hF : Measurable F) (hG : Measurable G) :
    Measure.map (fun U => (F (vertexSampler f U), G (vertexSampler g U)))
        (labelMeasure d) =
      (Measure.map F (Measure.infinitePi (fun _ : TreeVertex d => μ))).prod
        (Measure.map G (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  rw [Measure.map_prod_map _ _ hF hG,
    ← map_independent_vertexSamplers (d := d) μ ν hf hg hlaw,
    Measure.map_map (hF.prodMap hG)
      ((measurable_vertexSampler hf).prodMk (measurable_vertexSampler hg))]
  rfl

theorem exists_independent_label_copies (d : ℕ) :
    ∃ F G : (TreeVertex d → ℝ) → (TreeVertex d → ℝ),
      Measurable F ∧ Measurable G ∧
      Measure.map (fun U => (F U, G U)) (labelMeasure d) =
        (labelMeasure d).prod (labelMeasure d) ∧
      (∀ a : TreeAut d, ∀ U, F (relabel a U) = relabel a (F U)) ∧
      (∀ a : TreeAut d, ∀ U, G (relabel a U) = relabel a (G U)) := by
  obtain ⟨f, g, hf, hg, hlaw⟩ :=
    exists_uniform01_independent_samplers uniform01 uniform01
  exact ⟨vertexSampler f, vertexSampler g,
    measurable_vertexSampler hf, measurable_vertexSampler hg,
    map_independent_vertexSamplers uniform01 uniform01 hf hg hlaw,
    vertexSampler_relabel f, vertexSampler_relabel g⟩

theorem isFactorOfIID_of_independent_product_inputs
    {d : ℕ} {theta : ℝ} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [Nonempty α] [Nonempty β] [StandardBorelSpace α] [StandardBorelSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : ((TreeVertex d → α) × (TreeVertex d → β)) → (TreeVertex d → IsingSpin))
    (hH : Measurable H)
    (hLaw : HasFreeIsingLaw theta (Measure.map H
      ((Measure.infinitePi (fun _ : TreeVertex d => μ)).prod
        (Measure.infinitePi (fun _ : TreeVertex d => ν)))))
    (hEquiv : ∀ a : TreeAut d,
      ∀ᵐ p ∂(Measure.infinitePi (fun _ : TreeVertex d => μ)).prod
        (Measure.infinitePi (fun _ : TreeVertex d => ν)),
        H (relabel a p.1, relabel a p.2) = relabel a (H p)) :
    IsFactorOfIID d theta := by
  obtain ⟨f, g, hf, hg, hlaw⟩ := exists_uniform01_independent_samplers μ ν
  let S := fun U => (vertexSampler (d := d) f U, vertexSampler g U)
  have hS : Measurable S :=
    (measurable_vertexSampler hf).prodMk (measurable_vertexSampler hg)
  have hSlaw := map_independent_vertexSamplers (d := d) μ ν hf hg hlaw
  refine ⟨H ∘ S, hH.comp hS, ?_, ?_⟩
  · rw [← Measure.map_map hH hS, hSlaw]
    exact hLaw
  · intro a
    have h : ∀ᵐ p ∂Measure.map S (labelMeasure d),
        H (relabel a p.1, relabel a p.2) = relabel a (H p) := by
      rw [hSlaw]
      exact hEquiv a
    filter_upwards [ae_of_ae_map hS.aemeasurable h] with U hU
    exact hU

end Problem367

end

end OAI
