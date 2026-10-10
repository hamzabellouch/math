import OAI.Probability.DirectionalWalk.BufferEntropy

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section BufferKernelTransforms
variable {Θ A B Δ G : Type*} [Countable Θ] [Countable A] [Countable B] [Countable Δ] [Countable G]
  [MeasurableSpace Θ] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Δ] [MeasurableSpace G]
  [MeasurableSingletonClass Θ] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [MeasurableSingletonClass Δ] [MeasurableSingletonClass G]

lemma compProd_swap_inner (η : Measure Θ) [IsProbabilityMeasure η]
    (κA : Kernel Θ A) (κB : Kernel Θ B) [IsMarkovKernel κA] [IsMarkovKernel κB] :
    (η ⊗ₘ (κA ×ₖ κB)).map (fun p => ((p.1,p.2.2),p.2.1)) =
      (η ⊗ₘ κB) ⊗ₘ κA.comap Prod.fst measurable_fst := by
  apply Measure.ext_of_singleton
  rintro ⟨⟨h,b⟩,a⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hs : (fun p : Θ × (A × B) => ((p.1,p.2.2),p.2.1)) ⁻¹' {((h,b),a)} = {(h,(a,b))} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.ext_iff]
    tauto
  rw [hs,compProd_atom,compProd_atom,compProd_atom,Kernel.comap_apply,Kernel.prod_apply,
    ← Set.singleton_prod_singleton,Measure.prod_prod]
  ring

lemma compProd_prod_buffer (η : Measure Θ) [IsProbabilityMeasure η]
    (κ : Kernel Θ A) [IsMarkovKernel κ] (π : Measure Δ) [IsProbabilityMeasure π] :
    ((η ⊗ₘ κ).prod π).map (fun p => (p.1.1,(p.2,p.1.2))) =
      η ⊗ₘ ((Kernel.const Θ π) ×ₖ κ) := by
  apply Measure.ext_of_singleton
  rintro ⟨h,d,a⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hs : (fun p : (Θ × A) × Δ => (p.1.1,(p.2,p.1.2))) ⁻¹' {(h,(d,a))} = {((h,a),d)} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.ext_iff]
    tauto
  rw [hs,← Set.singleton_prod_singleton,Measure.prod_prod,compProd_atom,compProd_atom,
    Kernel.prod_apply,Kernel.const_apply,← Set.singleton_prod_singleton,Measure.prod_prod]
  ring

omit [Countable G] [MeasurableSingletonClass G] in
lemma buffer_reference_map (η : Measure Θ) [IsProbabilityMeasure η]
    (κA : Kernel Θ A) (κB : Kernel Θ B) [IsMarkovKernel κA] [IsMarkovKernel κB]
    (π : Measure Δ) [IsProbabilityMeasure π] (F : Δ × A → G) :
    ((η ⊗ₘ (κA ×ₖ κB)).prod π).map (fun p => ((p.1.1,p.1.2.2),F (p.2,p.1.2.1))) =
      (η ⊗ₘ κB) ⊗ₘ (((Kernel.const Θ π ×ₖ κA).map F).comap Prod.fst measurable_fst) := by
  let f := fun p : Θ × (A × B) => ((p.1,p.2.2),p.2.1)
  let g := fun p : ((Θ × B) × A) × Δ => (p.1.1,(p.2,p.1.2))
  have h1 : ((η ⊗ₘ (κA ×ₖ κB)).prod π).map (Prod.map f id) =
      (((η ⊗ₘ κB) ⊗ₘ κA.comap Prod.fst measurable_fst).prod π) := by
    rw [← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id,Measure.map_id,
      compProd_swap_inner]
  have h2 := compProd_prod_buffer (η ⊗ₘ κB) (κA.comap Prod.fst measurable_fst) π
  have hk : ((Kernel.const (Θ × B) π) ×ₖ κA.comap Prod.fst measurable_fst).map F =
      ((Kernel.const Θ π ×ₖ κA).map F).comap Prod.fst measurable_fst := by
    ext p s hs
    simp only [Kernel.map_apply _ (measurable_of_countable F),Kernel.comap_apply,
      Kernel.prod_apply,Kernel.const_apply]
  rw [← hk,Measure.compProd_map (measurable_of_countable F),← h2,← h1,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

omit [Countable G] [MeasurableSingletonClass G] in
lemma buffer_data_processing (ρ : Measure (Θ × (A × B))) [IsProbabilityMeasure ρ]
    (η : Measure Θ) [IsProbabilityMeasure η] (κA : Kernel Θ A) (κB : Kernel Θ B)
    [IsMarkovKernel κA] [IsMarkovKernel κB]
    (π : Measure Δ) [IsProbabilityMeasure π] (F : Δ × A → G) :
    InformationTheory.klDiv
      ((ρ.prod π).map (fun p => ((p.1.1,p.1.2.2),F (p.2,p.1.2.1))))
      ((η ⊗ₘ κB) ⊗ₘ (((Kernel.const Θ π ×ₖ κA).map F).comap Prod.fst measurable_fst)) ≤
      InformationTheory.klDiv ρ (η ⊗ₘ (κA ×ₖ κB)) := by
  rw [← buffer_reference_map]
  apply (InformationTheory.klDiv_map_le _ _ (measurable_of_countable _)).trans
  rw [klDiv_product,InformationTheory.klDiv_self,add_zero]

lemma conditional_buffer_information (ρ : Measure (Θ × (A × B))) [IsProbabilityMeasure ρ]
    (η : Measure Θ) [IsProbabilityMeasure η] (κA : Kernel Θ A) (κB : Kernel Θ B)
    [IsMarkovKernel κA] [IsMarkovKernel κB] [Nonempty G]
    (π : Measure Δ) [IsProbabilityMeasure π] (F : Δ × A → G)
    (hfin : InformationTheory.klDiv ρ (η ⊗ₘ (κA ×ₖ κB)) ≠ ∞)
    (hZ : Integrable (informationOf (ρ.prod π) (fun p => F (p.2,p.1.2.1))) (ρ.prod π)) :
    conditionedEntropy (ρ.prod π) (fun p => F (p.2,p.1.2.1)) (fun p => p.1.1) -
      conditionedEntropy (ρ.prod π) (fun p => F (p.2,p.1.2.1)) (fun p => (p.1.1,p.1.2.2)) ≤
      (InformationTheory.klDiv ρ (η ⊗ₘ (κA ×ₖ κB))).toReal := by
  let K := ((Kernel.const Θ π ×ₖ κA).map F)
  let : IsMarkovKernel K := Kernel.IsMarkovKernel.map _ (measurable_of_countable F)
  let f := fun p : (Θ × (A × B)) × Δ => ((p.1.1,p.1.2.2),F (p.2,p.1.2.1))
  let P := (ρ.prod π).map f
  have : IsProbabilityMeasure P := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hle := buffer_data_processing ρ η κA κB π F
  have hn : InformationTheory.klDiv P ((η ⊗ₘ κB) ⊗ₘ K.comap Prod.fst measurable_fst) ≠ ∞ :=
    ne_top_of_le_ne_top hfin hle
  have hi : Integrable (informationOf P Prod.snd) P := by
    rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable]
    change Integrable (informationOf ((ρ.prod π).map f) Prod.snd ∘ f) (ρ.prod π)
    rw [informationOf_map]
    exact hZ
  have hh := conditional_mutualInformation_le_reference P (η ⊗ₘ κB) Prod.fst K hn hi
  rw [conditionedEntropy_map,conditionedEntropy_map] at hh
  exact hh.trans (ENNReal.toReal_mono hfin hle)
end BufferKernelTransforms

section BufferedComparison
variable {Θ A B G : Type*} [Countable Θ] [Countable A] [Countable B] [Countable G]
  [MeasurableSpace Θ] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace G]
  [MeasurableSingletonClass Θ] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [MeasurableSingletonClass G] [AddCommGroup G]

omit [Countable A] [Countable G] [MeasurableSingletonClass A]
  [MeasurableSingletonClass G] [AddCommGroup G] in
lemma map_prod_snd_function (π : Measure A) (ρ : Measure B) [IsProbabilityMeasure π]
    [IsProbabilityMeasure ρ] (f : B → G) : (π.prod ρ).map (f ∘ Prod.snd) = ρ.map f := by
  rw [← Measure.map_map (measurable_of_countable _) measurable_snd,Measure.map_snd_prod,
    measure_univ,one_smul]

lemma buffered_reference_comparison (π : Measure (ℕ × G)) (ρ : Measure (A × B))
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (H : A × B → Θ) (DA : A → G) (DB : B → G) (C : A × B → ℕ)
    (κA : Kernel Θ A) (κB : Kernel Θ B) [IsMarkovKernel κA] [IsMarkovKernel κB]
    (hfin : InformationTheory.klDiv (ρ.map (fun a => (H a,a))) (ρ.map H ⊗ₘ (κA ×ₖ κB)) ≠ ∞)
    (hU : Integrable (informationOf π Prod.fst) π)
    (hd : Integrable (informationOf π Prod.snd) π)
    (hZ : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.2+DA ω.2.1)) (π.prod ρ))
    (hT : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.1+C ω.2)) (π.prod ρ))
    (hS : Integrable (informationOf (π.prod ρ) (fun ω => ω.1.2+DA ω.2.1+DB ω.2.2)) (π.prod ρ)) :
    let P := (π.prod ρ).map (fun ω => ((H ω.2,ω.1.2+DA ω.2.1),ω.2))
    let Q := P.fst ⊗ₘ (κA ×ₖ κB).comap Prod.fst measurable_fst
    InformationTheory.klDiv P Q ≠ ∞ ∧
      (InformationTheory.klDiv P Q).toReal ≤
        2*(InformationTheory.klDiv (ρ.map (fun a => (H a,a))) (ρ.map H ⊗ₘ (κA ×ₖ κB))).toReal +
        entropyOf (π.prod ρ) (fun ω => (ω.1.2+DA ω.2.1+DB ω.2.2,ω.1.1+C ω.2)) -
        entropyOf π (fun p => (p.2,p.1)) := by
  dsimp only
  let R := ρ.map (fun a => (H a,a))
  let η := ρ.map H
  have : IsProbabilityMeasure R := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure η := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hb : (π.prod ρ).map (fun ω => (H ω.2,ω.2)) = R :=
    map_prod_snd_function π ρ (fun a => (H a,a))
  have hf : R.fst = η := map_graph_fst ρ H
  have he : R.prod π = (π.prod ρ).map (fun p => ((H p.2,p.2),p.1)) := by
    calc
      R.prod π = (ρ.map (fun a => (H a,a))).prod (π.map id) := by rw [Measure.map_id]
      _ = (ρ.prod π).map (Prod.map (fun a => (H a,a)) id) :=
        Measure.map_prod_map ρ π (measurable_of_countable _) measurable_id
      _ = _ := by
        rw [← Measure.prod_swap (μ := π) (ν := ρ),Measure.map_map (measurable_of_countable _) measurable_swap]
        rfl
  have hz' : Integrable (informationOf (R.prod π) (fun p => p.2.2+DA p.1.2.1)) (R.prod π) := by
    rw [he,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable]
    rw [informationOf_map]
    exact hZ
  have hI := conditional_buffer_information R η κA κB π (fun p => p.1.2+DA p.2) hfin hz'
  rw [he,conditionedEntropy_map,conditionedEntropy_map] at hI
  have hc := buffer_entropy_chain π ρ H Prod.snd (fun a => DA a.1) DB C hT hS
    (InformationTheory.klDiv R (η ⊗ₘ (κA ×ₖ κB))).toReal hI
  have hbase : InformationTheory.klDiv ((π.prod ρ).map (fun ω => (H ω.2,ω.2)))
      (((π.prod ρ).map (fun ω => (H ω.2,ω.2))).fst ⊗ₘ (κA ×ₖ κB)) ≠ ∞ := by
    rwa [hb,hf]
  have haug := klDiv_reference_augment (π.prod ρ) Prod.snd (H ∘ Prod.snd)
    (fun ω => ω.1.2+DA ω.2.1) (κA ×ₖ κB)
    (InformationTheory.klDiv_ne_top_iff.mp hbase).1
    (InformationTheory.klDiv_ne_top_iff.mp hbase).2 hZ
  dsimp only [Function.comp_apply] at haug
  rw [hb,hf,buffer_displacement_entropy π ρ H (fun a => DA a.1)] at haug
  rw [entropyOf_pair_chain π Prod.snd Prod.fst hd
    (integrable_conditionedInformation π Prod.fst Prod.snd hU)]
  refine ⟨haug.1,?_⟩
  rw [haug.2]
  dsimp only [R,η,Function.comp_def] at hc ⊢
  linarith
end BufferedComparison

end DirectionalZeroOne

end OAI
