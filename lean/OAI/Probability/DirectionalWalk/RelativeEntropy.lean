import OAI.Probability.DirectionalWalk.EntropyBounds

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma llr_conditional_reference {α β : Type*} [Countable α] [Countable β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ] (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : ρ ≪ ρ.fst ⊗ₘ κ) :
    llr ρ (ρ.fst ⊗ₘ κ) =ᵐ[ρ] fun p => atomInfo (κ p.1) p.2 - conditionalInfo ρ p := by
  filter_upwards [llr_atom ρ (ρ.fst ⊗ₘ κ) hac,ae_atom_real_pos ρ,
    hac (ae_atom_real_pos (ρ.fst ⊗ₘ κ)),conditionalInfo_log ρ] with p hllr hp hν he
  have hfst : 0 < ρ.fst.real {p.1} := hp.trans_le (ENNReal.toReal_mono (by finiteness) (atom_le_fst ρ p))
  have hn : (ρ.fst ⊗ₘ κ).real {p} = ρ.fst.real {p.1} * (κ p.1).real {p.2} := by
    simp only [measureReal_def,compProd_atom,ENNReal.toReal_mul]
  have hk : 0 < (κ p.1).real {p.2} := (mul_pos_iff_of_pos_left hfst).mp (hn ▸ hν)
  rw [hllr,hn,Real.log_mul hfst.ne' hk.ne',he]
  dsimp [atomInfo]
  ring

lemma llr_reference_pullback {Ω α β : Type*} [Countable Ω] [Countable α] [Countable β]
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → β) (Y : Ω → α)
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : μ.map (fun ω => (Y ω,X ω)) ≪ (μ.map (fun ω => (Y ω,X ω))).fst ⊗ₘ κ) :
    (fun ω => llr (μ.map (fun ω => (Y ω,X ω)))
      ((μ.map (fun ω => (Y ω,X ω))).fst ⊗ₘ κ) (Y ω,X ω)) =ᵐ[μ]
      fun ω => atomInfo (κ (Y ω)) (X ω) - conditionedInformation μ X Y ω := by
  let F := fun ω => (Y ω,X ω)
  have : IsProbabilityMeasure (μ.map F) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hF : MeasurePreserving F μ (μ.map F) := ⟨measurable_of_countable _,rfl⟩
  filter_upwards [hF.quasiMeasurePreserving.ae (llr_conditional_reference (μ.map F) κ hac),
    conditionedInformation_eq μ X Y] with ω hω hω'
  rw [hω,hω']

lemma reference_ac_lift {α β γ : Type*} [Countable α] [Countable β] [Countable γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure ((α × γ) × β)) [IsProbabilityMeasure ρ]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : ρ.map (fun p => (p.1.1,p.2)) ≪ (ρ.map (fun p => (p.1.1,p.2))).fst ⊗ₘ κ) :
    ρ ≪ ρ.fst ⊗ₘ κ.comap Prod.fst measurable_fst := by
  apply absolutelyContinuous_of_atoms
  intro p hp
  by_contra hn
  have hfst : ρ.fst {p.1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le (atom_le_fst ρ p))
  have hm : ρ.map (fun p => (p.1.1,p.2)) {(p.1.1,p.2)} ≠ 0 :=
    ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le (atom_le_map ρ _ (measurable_of_countable _) p))
  have hq : ((ρ.map (fun p => (p.1.1,p.2))).fst ⊗ₘ κ) {(p.1.1,p.2)} ≠ 0 := fun h => hm (hac h)
  rw [compProd_atom] at hq
  rw [compProd_atom,Kernel.comap_apply] at hp
  exact (mul_ne_zero hfst (mul_ne_zero_iff.mp hq).2) hp

lemma conditionedInformation_swap_chain {Ω α β γ : Type*} [Countable Ω]
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    (fun ω => conditionedInformation μ X Y ω - conditionedInformation μ X (fun ξ => (Y ξ,Z ξ)) ω) =
      fun ω => conditionedInformation μ Z Y ω - conditionedInformation μ Z (fun ξ => (Y ξ,X ξ)) ω := by
  have hswap : informationOf μ (fun ω => ((Y ω,Z ω),X ω)) =
      informationOf μ (fun ω => ((Y ω,X ω),Z ω)) := by
    funext ξ
    rw [informationOf_fiber,informationOf_fiber]
    congr 3
    ext ζ
    simp [and_assoc,and_comm]
  funext ω
  simp only [conditionedInformation,hswap]
  ring

lemma klDiv_reference_augment {Ω α β γ : Type*} [Countable Ω] [Countable α] [Countable β]
    [Countable γ] [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → β) (H : Ω → α) (Z : Ω → γ)
    (κ : Kernel α β) [IsMarkovKernel κ]
    (hac : μ.map (fun ω => (H ω,X ω)) ≪ (μ.map (fun ω => (H ω,X ω))).fst ⊗ₘ κ)
    (hi : Integrable (llr (μ.map (fun ω => (H ω,X ω)))
      ((μ.map (fun ω => (H ω,X ω))).fst ⊗ₘ κ)) (μ.map (fun ω => (H ω,X ω))))
    (hZ : Integrable (informationOf μ Z) μ) :
    let P := μ.map (fun ω => ((H ω,Z ω),X ω))
    let Q := P.fst ⊗ₘ κ.comap Prod.fst measurable_fst
    InformationTheory.klDiv P Q ≠ ∞ ∧
      (InformationTheory.klDiv P Q).toReal =
        (InformationTheory.klDiv (μ.map (fun ω => (H ω,X ω)))
          ((μ.map (fun ω => (H ω,X ω))).fst ⊗ₘ κ)).toReal +
        conditionedEntropy μ Z H - conditionedEntropy μ Z (fun ω => (H ω,X ω)) := by
  dsimp only
  let F := fun ω => (H ω,X ω)
  let G := fun ω => ((H ω,Z ω),X ω)
  let P := μ.map G
  let P₀ := μ.map F
  let Q := P.fst ⊗ₘ κ.comap Prod.fst measurable_fst
  let Q₀ := P₀.fst ⊗ₘ κ
  have : IsProbabilityMeasure P := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have : IsProbabilityMeasure P₀ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hac' : P ≪ Q := by
    apply reference_ac_lift
    simpa only [P,G,Measure.map_map (measurable_of_countable _) (measurable_of_countable _),Function.comp_def] using hac
  have hF : MeasurePreserving F μ P₀ := ⟨measurable_of_countable _,rfl⟩
  have hG : MeasurePreserving G μ P := ⟨measurable_of_countable _,rfl⟩
  have he : (fun ω => llr P Q (G ω)) =ᵐ[μ]
      fun ω => llr P₀ Q₀ (F ω) + conditionedInformation μ Z H ω -
        conditionedInformation μ Z (fun ξ => (H ξ,X ξ)) ω := by
    filter_upwards [llr_reference_pullback μ X H κ hac,
      llr_reference_pullback μ X (fun ω => (H ω,Z ω)) (κ.comap Prod.fst measurable_fst) hac'] with ω h0 h1
    have hs := congrFun (conditionedInformation_swap_chain μ X H Z) ω
    simp only [Kernel.comap_apply] at h1
    change llr P₀ Q₀ (F ω) = _ at h0
    change llr P Q (G ω) = _ at h1
    linarith
  have hiF : Integrable (fun ω => llr P₀ Q₀ (F ω)) μ := hF.integrable_comp_of_integrable hi
  have hiZH := integrable_conditionedInformation μ Z H hZ
  have hiZX := integrable_conditionedInformation μ Z (fun ω => (H ω,X ω)) hZ
  have hiG : Integrable (fun ω => llr P Q (G ω)) μ := ((hiF.add hiZH).sub hiZX).congr he.symm
  have hiP : Integrable (llr P Q) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr hiG
  refine ⟨InformationTheory.klDiv_ne_top hac' hiP, ?_⟩
  have hq := InformationTheory.toReal_klDiv hac' hiP
  have hq0 := InformationTheory.toReal_klDiv hac hi
  simp only [probReal_univ,add_sub_cancel_right] at hq hq0
  change (InformationTheory.klDiv P Q).toReal = (InformationTheory.klDiv P₀ Q₀).toReal + _ - _
  rw [hq,hq0]
  have hInt : (∫ p, llr P Q p ∂P) = ∫ ω, llr P Q (G ω) ∂μ :=
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable
  have hInt0 : (∫ p, llr P₀ Q₀ p ∂P₀) = ∫ ω, llr P₀ Q₀ (F ω) ∂μ :=
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable
  rw [hInt,hInt0,integral_congr_ae he]
  calc
    _ = (∫ ω, llr P₀ Q₀ (F ω) + conditionedInformation μ Z H ω ∂μ) -
        ∫ ω, conditionedInformation μ Z (fun ξ => (H ξ,X ξ)) ω ∂μ :=
      integral_sub (hiF.add hiZH) hiZX
    _ = _ := by
      congr 1
      exact integral_add hiF hiZH

lemma reference_ac_projection {α β γ : Type*} [Countable α] [Countable β] [Countable γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure (α × γ)) [IsProbabilityMeasure ρ] (f : α → β)
    (κ : Kernel β γ) [IsMarkovKernel κ]
    (hac : ρ ≪ ρ.fst ⊗ₘ κ.comap f (measurable_of_countable _)) :
    ρ.map (fun p => (f p.1,p.2)) ≪ (ρ.map (fun p => (f p.1,p.2))).fst ⊗ₘ κ := by
  let F := fun p : α × γ => (f p.1,p.2)
  let ν := ρ.map F
  apply absolutelyContinuous_of_atoms
  intro p hp
  by_contra hn
  have hm : ν.fst {p.1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le (atom_le_fst ν p))
  rw [compProd_atom] at hp
  have hk : κ p.1 {p.2} = 0 := (mul_eq_zero.mp hp).resolve_left hm
  apply hn
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← Set.biUnion_of_singleton (F ⁻¹' {p})]
  apply (measure_biUnion_null_iff (Set.to_countable _)).mpr
  intro x hx
  have he : F x = p := hx
  apply hac
  rw [compProd_atom,Kernel.comap_apply]
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  dsimp [F] at he1 he2
  rw [he1,he2,hk,mul_zero]

lemma conditional_mutualInformation_le_reference {α β γ : Type*}
    [Countable α] [Countable β] [Countable γ] [Nonempty γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure (α × γ)) [IsProbabilityMeasure ρ] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → β) (κ : Kernel β γ) [IsMarkovKernel κ]
    (hfin : InformationTheory.klDiv ρ (ν ⊗ₘ κ.comap f (measurable_of_countable _)) ≠ ∞)
    (hZ : Integrable (informationOf ρ Prod.snd) ρ) :
    conditionedEntropy ρ Prod.snd (f ∘ Prod.fst) - conditionedEntropy ρ Prod.snd Prod.fst ≤
      (InformationTheory.klDiv ρ (ν ⊗ₘ κ.comap f (measurable_of_countable _))).toReal := by
  let η := κ.comap f (measurable_of_countable _)
  have hchain := InformationTheory.klDiv_compProd_eq_add ρ.fst ν ρ.condKernel η
  rw [Measure.disintegrate] at hchain
  have hle : InformationTheory.klDiv ρ (ρ.fst ⊗ₘ η) ≤ InformationTheory.klDiv ρ (ν ⊗ₘ η) := by
    rw [hchain]
    exact le_add_self
  have hfin' : InformationTheory.klDiv ρ (ρ.fst ⊗ₘ η) ≠ ∞ := ne_top_of_le_ne_top hfin hle
  obtain ⟨hac,hi⟩ := InformationTheory.klDiv_ne_top_iff.mp hfin'
  have hid : ρ.map (fun p : α × γ => (p.1,p.2)) = ρ := by
    change ρ.map id = ρ
    exact Measure.map_id
  have hce : conditionedInformation ρ Prod.snd Prod.fst =ᵐ[ρ] conditionalInfo ρ := by
    simpa only [hid,Prod.mk.eta] using conditionedInformation_eq ρ Prod.snd Prod.fst
  have hci : Integrable (conditionalInfo ρ) ρ :=
    (integrable_conditionedInformation ρ Prod.snd Prod.fst hZ).congr hce
  have hc : Integrable (fun p : α × γ => atomInfo (κ (f p.1)) p.2) ρ := by
    apply (hi.add hci).congr
    filter_upwards [llr_conditional_reference ρ η hac] with p hp
    simpa only [Pi.add_apply,η,Kernel.comap_apply,sub_add_cancel] using congrArg (fun x => x + conditionalInfo ρ p) hp
  let F := fun p : α × γ => (f p.1,p.2)
  let P := ρ.map F
  have : IsProbabilityMeasure P := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hcP : Integrable (fun p : β × γ => atomInfo (κ p.1) p.2) P := by
    exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr hc
  have hg := conditionalEntropy_le_crossEntropy P κ (reference_ac_projection ρ f κ hac) hcP
  have heP : conditionedEntropy ρ Prod.snd (f ∘ Prod.fst) = conditionalEntropy P := by
    exact conditionedEntropy_eq_conditionalEntropy ρ Prod.snd (f ∘ Prod.fst)
  have heρ : conditionedEntropy ρ Prod.snd Prod.fst = conditionalEntropy ρ := by
    rw [conditionedEntropy_eq_conditionalEntropy,hid]
  have heI : (∫ p, atomInfo (κ p.1) p.2 ∂P) = ∫ p : α × γ, atomInfo (κ (f p.1)) p.2 ∂ρ :=
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable
  have hkl := InformationTheory.toReal_klDiv hac hi
  simp only [probReal_univ,add_sub_cancel_right] at hkl
  have hint : (∫ p, llr ρ (ρ.fst ⊗ₘ η) p ∂ρ) =
      (∫ p : α × γ, atomInfo (κ (f p.1)) p.2 ∂ρ) - conditionalEntropy ρ := by
    rw [integral_congr_ae (llr_conditional_reference ρ η hac)]
    exact integral_sub hc hci
  rw [heI] at hg
  rw [heP,heρ]
  calc
    _ ≤ (InformationTheory.klDiv ρ (ρ.fst ⊗ₘ η)).toReal := by rw [hkl,hint]; linarith
    _ ≤ _ := ENNReal.toReal_mono hfin hle

end DirectionalZeroOne

end OAI
