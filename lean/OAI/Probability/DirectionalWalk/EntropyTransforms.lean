import OAI.Probability.DirectionalWalk.Information

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma atom_le_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) (f : α → β) (hf : Measurable f) (x : α) :
    μ {x} ≤ μ.map f {f x} := by
  rw [Measure.map_apply hf (measurableSet_singleton _)]
  exact measure_mono (by intro y hy; obtain rfl := Set.mem_singleton_iff.mp hy; rfl)

lemma conditionalInfo_eq_kernel {α β : Type*} [Countable α] [Countable β] [Nonempty β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (p : α × β) (hp : ρ.fst {p.1} ≠ 0) :
    atomInfo (ρ.condKernel p.1) p.2 = conditionalInfo ρ p := by
  dsimp [atomInfo,conditionalInfo,measureReal_def]
  rw [Measure.condKernel_apply_of_ne_zero hp,Set.singleton_prod_singleton,ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  congr 1
  ring_nf

lemma ac_conditioning_projection {α β γ : Type*} [Countable α] [Countable β] [Countable γ]
    [Nonempty γ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure (α × γ)) [IsProbabilityMeasure ρ] (f : α → β) :
    ρ ≪ ρ.fst ⊗ₘ (ρ.map (fun p => (f p.1,p.2))).condKernel.comap f (measurable_of_countable _) := by
  let ν := ρ.map (fun p => (f p.1,p.2))
  apply absolutelyContinuous_of_atoms
  intro p hp
  by_contra hn
  have hfst : ρ.fst {p.1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le (atom_le_fst ρ p))
  have hold : ν {(f p.1,p.2)} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hn).trans_le
    (atom_le_map ρ (fun p => (f p.1,p.2)) (measurable_of_countable _) p))
  have hmarg : ν.fst {f p.1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hold).trans_le (atom_le_fst ν (f p.1,p.2)))
  rw [compProd_atom,Kernel.comap_apply] at hp
  have hk : ν.condKernel (f p.1) {p.2} ≠ 0 := by
    rw [Measure.condKernel_apply_of_ne_zero hmarg,Set.singleton_prod_singleton]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (by finiteness)) hold
  exact (mul_ne_zero hfst hk) hp

lemma conditionedEntropy_monotone_projection {α β γ : Type*} [Countable α] [Countable β]
    [Countable γ] [Nonempty γ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (ρ : Measure (α × γ)) [IsProbabilityMeasure ρ] (f : α → β)
    (hi : Integrable (conditionalInfo (ρ.map (fun p => (f p.1,p.2)))) (ρ.map (fun p => (f p.1,p.2)))) :
    conditionalEntropy ρ ≤ conditionalEntropy (ρ.map (fun p => (f p.1,p.2))) := by
  let F := fun p : α × γ => (f p.1,p.2)
  let ν := ρ.map F
  let κ := ν.condKernel.comap f (measurable_of_countable _)
  have hF : MeasurePreserving F ρ ν := ⟨measurable_of_countable _,rfl⟩
  have he : (fun p : α × γ => atomInfo (κ p.1) p.2) =ᵐ[ρ] fun p => conditionalInfo ν (F p) := by
    filter_upwards [hF.quasiMeasurePreserving.ae (ae_atom_pos ν)] with p hp
    have hm : ν.fst {(F p).1} ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hp).trans_le (atom_le_fst ν (F p)))
    exact conditionalInfo_eq_kernel ν (F p) hm
  have hc := (hF.integrable_comp_of_integrable hi).congr he.symm
  have hh := conditionalEntropy_le_crossEntropy ρ κ (ac_conditioning_projection ρ f) hc
  rw [integral_congr_ae he] at hh
  have hi' : (∫ p, conditionalInfo ν (F p) ∂ρ) = conditionalEntropy ν := by
    dsimp [conditionalEntropy,ν]
    rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]
  exact hh.trans_eq hi'

lemma conditionedEntropy_eq_conditionalEntropy {Ω α β : Type*} [Countable Ω] [Countable α]
    [Countable β] [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) :
    conditionedEntropy μ X Y = conditionalEntropy (μ.map (fun ω => (Y ω,X ω))) := by
  dsimp [conditionedEntropy,conditionalEntropy]
  rw [integral_congr_ae (conditionedInformation_eq μ X Y),
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]

lemma conditionedEntropy_le_conditionedEntropy {Ω α β γ : Type*} [Countable Ω] [Countable α]
    [Countable β] [Countable γ] [Nonempty α] [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSingletonClass Ω]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (hi : Integrable (informationOf μ X) μ) :
    conditionedEntropy μ X (fun ω => (Y ω,Z ω)) ≤ conditionedEntropy μ X Y := by
  rw [conditionedEntropy_eq_conditionalEntropy,conditionedEntropy_eq_conditionalEntropy]
  let ρ := μ.map (fun ω => ((Y ω,Z ω),X ω))
  have : IsProbabilityMeasure ρ := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have he : ρ.map (fun p => (p.1.1,p.2)) = μ.map (fun ω => (Y ω,X ω)) := by
    dsimp [ρ]
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  have hI : Integrable (conditionalInfo (μ.map (fun ω => (Y ω,X ω)))) (μ.map (fun ω => (Y ω,X ω))) := by
    rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable (measurable_of_countable _).aemeasurable]
    exact (integrable_conditionedInformation μ X Y hi).congr (conditionedInformation_eq μ X Y)
  have hh := conditionedEntropy_monotone_projection ρ Prod.fst (by rw [he]; exact hI)
  simpa only [he] using hh

section EntropyTransforms
variable {Ω α β γ : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Countable γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]

omit [Countable α] [MeasurableSingletonClass α] in
lemma informationOf_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (ω : Ω) :
    0 ≤ informationOf μ X ω := by
  have : IsProbabilityMeasure (μ.map X) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  exact atomInfo_nonneg _ _

omit [Countable β] in
lemma informationOf_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (f : α → β) :
    ∀ᵐ ω ∂μ, informationOf μ (f ∘ X) ω ≤ informationOf μ X ω := by
  have : IsProbabilityMeasure (μ.map X) := probabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hX : MeasurePreserving X μ (μ.map X) := ⟨measurable_of_countable _,rfl⟩
  filter_upwards [hX.quasiMeasurePreserving.ae (ae_atom_real_pos (μ.map X))] with ω hω
  have hm := atom_le_map (μ.map X) f (measurable_of_countable _) (X ω)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hm
  have hm' : (μ.map X).real {X ω} ≤ (μ.map (f ∘ X)).real {(f ∘ X) ω} :=
    ENNReal.toReal_mono (by finiteness) hm
  dsimp [informationOf,atomInfo]
  exact neg_le_neg (Real.log_le_log hω hm')

omit [Countable β] in
lemma integrable_informationOf_comp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (f : α → β) (hi : Integrable (informationOf μ X) μ) :
    Integrable (informationOf μ (f ∘ X)) μ := by
  apply hi.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [informationOf_comp_le μ X f] with ω hω
  simpa only [Real.norm_eq_abs,abs_of_nonneg (informationOf_nonneg μ (f ∘ X) ω)] using hω

omit [Countable β] in
lemma entropyOf_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (f : α → β) (hi : Integrable (informationOf μ X) μ) :
    entropyOf μ (f ∘ X) ≤ entropyOf μ X := by
  exact integral_mono_ae (integrable_informationOf_comp μ X f hi) hi (informationOf_comp_le μ X f)

omit [Countable α] [Countable β] [Countable γ] in
lemma conditionedInformation_fiberwise_injective (μ : Measure Ω) (X : Ω → α) (Y : Ω → β)
    (f : β → α → γ) (hf : ∀ y, Function.Injective (f y)) :
    conditionedInformation μ (fun ω => f (Y ω) (X ω)) Y = conditionedInformation μ X Y := by
  have he : informationOf μ (fun ω => (Y ω,f (Y ω) (X ω))) =
      informationOf μ (fun ω => (Y ω,X ω)) := by
    funext ω
    rw [informationOf_fiber,informationOf_fiber]
    congr 3
    ext ξ
    simp only [Set.mem_ofPred_eq,Prod.mk.injEq]
    constructor
    · rintro ⟨hy,hf'⟩
      exact ⟨hy,hf (Y ω) (by simpa only [hy] using hf')⟩
    · rintro ⟨hy,hx⟩
      simp [hy,hx]
  funext ω
  change informationOf μ (fun ξ => (Y ξ,f (Y ξ) (X ξ))) ω - informationOf μ Y ω =
    informationOf μ (fun ξ => (Y ξ,X ξ)) ω - informationOf μ Y ω
  rw [he]

lemma informationOf_pair_indep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hXY : X ⟂ᵢ[μ] Y) :
    informationOf μ (fun ω => (X ω,Y ω)) =ᵐ[μ] fun ω => informationOf μ X ω + informationOf μ Y ω := by
  have hX : MeasurePreserving X μ (μ.map X) := ⟨measurable_of_countable _,rfl⟩
  have hY : MeasurePreserving Y μ (μ.map Y) := ⟨measurable_of_countable _,rfl⟩
  filter_upwards [hX.quasiMeasurePreserving.ae (ae_atom_real_pos (μ.map X)),
    hY.quasiMeasurePreserving.ae (ae_atom_real_pos (μ.map Y))] with ω hx hy
  simp only [informationOf,atomInfo]
  rw [hXY.map_prod_eq_prod_map_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable,measureReal_def,← Set.singleton_prod_singleton,
    Measure.prod_prod,ENNReal.toReal_mul,← measureReal_def,← measureReal_def,
    Real.log_mul hx.ne' hy.ne']
  ring

lemma conditionedInformation_indep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hXY : X ⟂ᵢ[μ] Y) :
    conditionedInformation μ X Y =ᵐ[μ] informationOf μ X := by
  filter_upwards [informationOf_pair_indep μ Y X hXY.symm] with ω hω
  simp only [conditionedInformation,hω,add_sub_cancel_left]

lemma conditionedEntropy_indep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (hXY : X ⟂ᵢ[μ] Y) :
    conditionedEntropy μ X Y = entropyOf μ X := integral_congr_ae (conditionedInformation_indep μ X Y hXY)

lemma conditionedInformation_indep_pair (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) (hXYZ : (fun ω => (Y ω,X ω)) ⟂ᵢ[μ] Z) :
    conditionedInformation μ X (fun ω => (Y ω,Z ω)) =ᵐ[μ] conditionedInformation μ X Y := by
  have hYZ : Y ⟂ᵢ[μ] Z := by
    simpa only [Function.comp_def,id_eq] using hXYZ.comp measurable_fst measurable_id
  filter_upwards [informationOf_pair_indep μ (fun ω => (Y ω,X ω)) Z hXYZ,
    informationOf_pair_indep μ Y Z hYZ] with ω hω hω'
  have hswap : informationOf μ (fun ω => ((Y ω,Z ω),X ω)) =
      informationOf μ (fun ω => ((Y ω,X ω),Z ω)) := by
    funext ξ
    rw [informationOf_fiber,informationOf_fiber]
    congr 3
    ext ζ
    simp [and_assoc,and_comm]
  simp only [conditionedInformation,hswap,hω,hω']
  ring

lemma conditionedEntropy_indep_pair (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) (hXYZ : (fun ω => (Y ω,X ω)) ⟂ᵢ[μ] Z) :
    conditionedEntropy μ X (fun ω => (Y ω,Z ω)) = conditionedEntropy μ X Y :=
  integral_congr_ae (conditionedInformation_indep_pair μ X Y Z hXYZ)

end EntropyTransforms

end DirectionalZeroOne

end OAI
