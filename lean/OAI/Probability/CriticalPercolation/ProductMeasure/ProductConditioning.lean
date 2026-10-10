import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Variance
import OAI.Probability.CriticalPercolation.ProductMeasure.TailProduct

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

@[simp] lemma mem_forceOn (S σ ω : Set E) (e : E) :
    e∈forceOn S σ ω ↔ if e∈S then e∈σ else e∈ω := Iff.rfl

lemma measurable_forceOn_joint (S : Set E) :
    Measurable (fun z : Set E × Set E => forceOn S z.1 z.2) := by
  refine (@measurable_pi_iff (Set E × Set E) E (fun _ => Prop)
    inferInstance (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e∈S
  · simpa only [forceOn,ite_eq_left he,Function.comp_def] using (measurable_set_mem e).comp measurable_fst
  · simpa only [forceOn,ite_eq_right he,Function.comp_def] using (measurable_set_mem e).comp measurable_snd

lemma measurable_forceOn_joint_block (S : Set E) :
    @Measurable (Set E × Set E) (Set E)
      ((blockSigma S).prod inferInstance) inferInstance
      (fun z => forceOn S z.1 z.2) := by
  refine (@measurable_pi_iff (Set E × Set E) E (fun _ => Prop)
    ((blockSigma S).prod inferInstance) (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e∈S
  · have hm : @Measurable (Set E) Prop (blockSigma S) inferInstance
        (fun σ => e∈σ) := by
      apply measurable_iff_comap_le.mpr
      exact le_iSup_of_le e (le_iSup_of_le he le_rfl)
    simpa only [forceOn,ite_eq_left he,Function.comp_def] using hm.comp measurable_fst
  · simpa only [forceOn,ite_eq_right he,Function.comp_def] using (measurable_set_mem e).comp measurable_snd

lemma forceOn_resample_law (q : E → unitInterval) (S : Set E) :
    ((law q).prod (law q)).map (fun z : Set E × Set E => forceOn S z.1 z.2)=law q := by
  let f : Set E → Set E := forceOn Sᶜ ∅
  let g : Set E → Set E := forceOn S ∅
  have hf : Measurable f := measurable_forceOn _ _
  have hg : Measurable g := measurable_forceOn _ _
  have hfb : @Measurable (Set E) (Set E) (blockSigma S) inferInstance f := by
    have hh := measurable_forceOn_block Sᶜ (∅ : Set E)
    rw [compl_compl] at hh
    exact hh
  have hgb : @Measurable (Set E) (Set E) (blockSigma Sᶜ) inferInstance g :=
    measurable_forceOn_block S ∅
  have hi : IndepFun f g (law q) :=
    indep_of_indep_of_le (independent_blocks q S) hfb.comap_le hgb.comap_le
  have hm := hi.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hp := congrArg (Measure.map (fun z : Set E × Set E => forceOn S z.1 z.2)) hm
  rw [Measure.map_prod_map _ _ hf hg,Measure.map_map (measurable_forceOn_joint S)
    (hf.prodMk hg),Measure.map_map (measurable_forceOn_joint S) (hf.prodMap hg)] at hp
  have he1 : (fun z : Set E × Set E => forceOn S z.1 z.2) ∘ (fun ω => (f ω,g ω))=id := by
    funext ω
    ext e
    by_cases he : e∈S <;> simp [f,g,he]
  have he2 : (fun z : Set E × Set E => forceOn S z.1 z.2) ∘ Prod.map f g=
      (fun z : Set E × Set E => forceOn S z.1 z.2) := by
    funext z
    ext e
    by_cases he : e∈S <;> simp [f,g,he]
  rw [he1,he2,Measure.map_id] at hp
  exact hp.symm

def pinnedParameters (q : E → unitInterval) (S σ : Set E) : E → unitInterval :=
  fun e => if e∈S then if e∈σ then 1 else 0 else q e

lemma forceOn_map_law (q : E → unitInterval) (S σ : Set E) :
    (law q).map (forceOn S σ)=law (pinnedParameters q S σ) := by
  simp only [law_eq_infinitePi]
  have hm (e : E) : Measurable (fun b : Prop => if e∈S then e∈σ else b) := .of_discrete
  have h := Measure.infinitePi_map_pi (fun e => bitMeasure (q e)) hm
  change (Measure.infinitePi (fun e => bitMeasure (q e))).map
    (fun (ω : E → Prop) e => if e∈S then e∈σ else ω e)=
    Measure.infinitePi (fun e => bitMeasure (pinnedParameters q S σ e))
  rw [h]
  congr 1
  funext e
  by_cases he : e∈S
  · simp only [ite_eq_left he,Measure.map_const,measure_univ,one_smul]
    by_cases hs : e∈σ <;> simp [pinnedParameters,he,hs,bitMeasure]
  · simp [pinnedParameters,he]

def blockProbability (q : E → unitInterval) (S : Set E) (A : Set (Set E))
    (σ : Set E) : ℝ≥0∞ := law q ((forceOn S σ) ⁻¹' A)

lemma blockProbability_eq_lintegral (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (σ : Set E) :
    blockProbability q S A σ=∫⁻ ω, A.indicator (1 : Set E → ℝ≥0∞) (forceOn S σ ω) ∂law q := by
  unfold blockProbability
  rw [← lintegral_indicator_one (hA.preimage (measurable_forceOn S σ))]
  rfl

lemma blockProbability_le_one (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (σ : Set E) : blockProbability q S A σ≤1 := prob_le_one

lemma measurable_blockProbability (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    @Measurable (Set E) ℝ≥0∞ (blockSigma S) inferInstance (blockProbability q S A) := by
  have hI : @Measurable (Set E × Set E) ℝ≥0∞
      ((blockSigma S).prod Set.instMeasurableSpace) inferInstance
      (fun z => A.indicator (1 : Set E → ℝ≥0∞) (forceOn S z.1 z.2)) :=
    @Measurable.comp (Set E × Set E) (Set E) ℝ≥0∞
      ((blockSigma S).prod Set.instMeasurableSpace) Set.instMeasurableSpace inferInstance
      _ _ (measurable_const.indicator hA) (measurable_forceOn_joint_block S)
  have hm := @Measurable.lintegral_prod_right' (Set E) (Set E)
    (blockSigma S) Set.instMeasurableSpace (law q) inferInstance _ hI
  convert hm using 1
  funext σ
  exact blockProbability_eq_lintegral q S A hA σ

lemma blockProbability_monotone (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : IsUpperSet A) : Monotone (blockProbability q S A) := by
  intro σ τ hστ
  apply measure_mono
  intro ω hω
  apply hA _ hω
  intro e he
  by_cases hs : e∈S
  · have hh : e∈σ := by simpa only [mem_forceOn,ite_eq_left hs] using he
    simpa only [mem_forceOn,ite_eq_left hs] using hστ hh
  · simpa only [mem_forceOn,ite_eq_right hs] using he

lemma lintegral_blockProbability (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫⁻ σ, blockProbability q S A σ ∂law q)=law q A := by
  simp_rw [blockProbability_eq_lintegral q S A hA]
  have hm : Measurable (fun z : Set E × Set E =>
      A.indicator (1 : Set E → ℝ≥0∞) (forceOn S z.1 z.2)) :=
    (measurable_const.indicator hA).comp (measurable_forceOn_joint S)
  rw [← lintegral_prod _ hm.aemeasurable]
  have hi : Measurable (A.indicator (1 : Set E → ℝ≥0∞)) := measurable_const.indicator hA
  rw [← lintegral_map hi (measurable_forceOn_joint S),
    forceOn_resample_law,lintegral_indicator_one hA]

lemma blockSigma_eq_comap (S : Set E) :
    blockSigma S=MeasurableSpace.comap (fun σ : Set E => (Subtype.val ⁻¹' σ : Set S))
      Set.instMeasurableSpace := by
  change (⨆ e∈S, MeasurableSpace.comap (fun σ : Set E => e∈σ) inferInstance)=
    MeasurableSpace.comap (fun σ : Set E => (Subtype.val ⁻¹' σ : Set S))
      (⨆ e : S, MeasurableSpace.comap (fun σ : Set S => e∈σ) inferInstance)
  rw [MeasurableSpace.comap_iSup,iSup_subtype']
  congr 1
  funext e
  rw [MeasurableSpace.comap_comp]
  rfl

lemma block_event_forceOn (S : Set E) (B : Set (Set E))
    (hB : MeasurableSet[blockSigma S] B) (σ ω : Set E) :
    forceOn S σ ω∈B ↔ σ∈B := by
  rw [blockSigma_eq_comap] at hB
  obtain ⟨C,hC,rfl⟩ := hB
  have he : (Subtype.val ⁻¹' forceOn S σ ω : Set S)=Subtype.val ⁻¹' σ := by
    ext e
    simp only [mem_preimage,mem_forceOn,ite_eq_left e.property]
  change (Subtype.val ⁻¹' forceOn S σ ω)∈C ↔ (Subtype.val ⁻¹' σ)∈C
  rw [he]

lemma blockProbability_inter_block (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hB : MeasurableSet[blockSigma S] B) (σ : Set E) :
    blockProbability q S (A∩B) σ=B.indicator (blockProbability q S A) σ := by
  unfold blockProbability
  by_cases hσ : σ∈B
  · rw [Set.indicator_of_mem hσ]
    congr 1
    ext ω
    simp only [Set.mem_preimage,Set.mem_inter_iff,block_event_forceOn S B hB,hσ,and_true]
  · rw [Set.indicator_of_notMem hσ]
    have he : forceOn S σ ⁻¹' (A∩B)=∅ := by
      ext ω
      simp only [Set.mem_preimage,Set.mem_inter_iff,block_event_forceOn S B hB,hσ,
        and_false,Set.mem_empty_iff_false]
    rw [he,measure_empty]

lemma setLIntegral_blockProbability (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet[blockSigma S] B) :
    (∫⁻ σ in B, blockProbability q S A σ ∂law q)=law q (A∩B) := by
  have hmB := (blockSigma_le S) _ hB
  rw [← lintegral_indicator hmB]
  simp_rw [← blockProbability_inter_block q S A B hB]
  exact lintegral_blockProbability q S (A∩B) (hA.inter hmB)

lemma forceOn_absorb (S T σ τ : Set E) (hST : S⊆T) :
    forceOn T τ ∘ forceOn S σ=forceOn T τ := by
  funext ω
  ext e
  change (e∈forceOn T τ (forceOn S σ ω)) ↔ e∈forceOn T τ ω
  by_cases heT : e∈T
  · simp only [mem_forceOn,ite_eq_left heT]
  · have heS : e∉S := fun he => heT (hST he)
    simp only [mem_forceOn,ite_eq_right heT,ite_eq_right heS]

lemma blockProbability_pin_smaller (q : E → unitInterval) (S T σ : Set E)
    (hST : S⊆T) (A : Set (Set E)) (hA : MeasurableSet A) (τ : Set E) :
    blockProbability (pinnedParameters q S σ) T A τ=blockProbability q T A τ := by
  unfold blockProbability
  rw [← forceOn_map_law q S σ,Measure.map_apply (measurable_forceOn S σ)
    (hA.preimage (measurable_forceOn T τ)),← Set.preimage_comp,forceOn_absorb S T σ τ hST]

lemma lintegral_blockProbability_tower (q : E → unitInterval) (S T σ : Set E)
    (hST : S⊆T) (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫⁻ ω, blockProbability q T A (forceOn S σ ω) ∂law q)=blockProbability q S A σ := by
  have hm := (measurable_blockProbability q T A hA).mono (blockSigma_le T) le_rfl
  rw [← lintegral_map hm (measurable_forceOn S σ),forceOn_map_law]
  simp_rw [← blockProbability_pin_smaller q S T σ hST A hA]
  rw [lintegral_blockProbability _ T A hA]
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn S σ) hA]
  rfl

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
