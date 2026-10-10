import OAI.Probability.FreeIsing.Conditioning.Copies
import OAI.Probability.FreeIsing.Conditioning.KernelExtensionConditionalExpectation
import OAI.Probability.FreeIsing.Conditioning.Pullback
import OAI.Probability.FreeIsing.Estimates.KernelCompatibility

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter

namespace Problem367.ConditionalCopyImmersion

variable {W O P X : Type*}
  [mW : MeasurableSpace W] [mO : MeasurableSpace O]
  [mP : MeasurableSpace P] [mX : MeasurableSpace X]

theorem map_onePast
    (ρ : Measure W) [IsProbabilityMeasure ρ]
    (η : Kernel W O) [IsMarkovKernel η]
    (p : W → P) (hp : Measurable p)
    (past : O → X) (hpast : Measurable past)
    (κ : Kernel P X) [IsMarkovKernel κ]
    (hκ : (fun w => (η.map past) w) =ᵐ[ρ] (fun w => κ (p w))) :
    (ρ ⊗ₘ (η ×ₖ η)).map
        (fun q : W × (O × O) => ((q.1, q.2.1), past q.2.2)) =
      (ρ ⊗ₘ η) ⊗ₘ κ.comap (fun q : W × O => p q.1) (hp.comp measurable_fst) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop), Measure.lintegral_compProd (by fun_prop),
    Measure.lintegral_compProd hf, Measure.lintegral_compProd (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hκ] with w hw
  rw [Kernel.prod_apply, lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro o
  simp only [Kernel.comap_apply]
  rw [← hw, Kernel.map_apply _ hpast, lintegral_map (by fun_prop) hpast]

theorem swap_measurePreserving
    (ρ : Measure W) [IsProbabilityMeasure ρ]
    (η : Kernel W O) [IsMarkovKernel η] :
    MeasurePreserving (fun q : W × (O × O) => (q.1, (q.2.2, q.2.1)))
      (ρ ⊗ₘ (η ×ₖ η)) (ρ ⊗ₘ (η ×ₖ η)) := by
  refine ⟨by fun_prop, ?_⟩
  change (ρ ⊗ₘ (η ×ₖ η)).map (Prod.map id Prod.swap) = _
  rw [← Measure.compProd_map measurable_swap, Kernel.map_prod_swap]

theorem map_onePast_right
    (ρ : Measure W) [IsProbabilityMeasure ρ]
    (η : Kernel W O) [IsMarkovKernel η]
    (p : W → P) (hp : Measurable p)
    (past : O → X) (hpast : Measurable past)
    (κ : Kernel P X) [IsMarkovKernel κ]
    (hκ : (fun w => (η.map past) w) =ᵐ[ρ] (fun w => κ (p w))) :
    (ρ ⊗ₘ (η ×ₖ η)).map
        (fun q : W × (O × O) => ((q.1, q.2.2), past q.2.1)) =
      (ρ ⊗ₘ η) ⊗ₘ κ.comap (fun q : W × O => p q.1) (hp.comp measurable_fst) := by
  have hs := (swap_measurePreserving ρ η).map_eq
  have he := congrArg (fun m : Measure (W × (O × O)) =>
    m.map (fun q => ((q.1, q.2.1), past q.2.2))) hs
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at he
  exact he.trans (map_onePast ρ η p hp past hpast κ hκ)

theorem exists_past_kernel_of_reconstructible_split
    {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace X] [Nonempty X]
    (ρ : Measure W) [IsProbabilityMeasure ρ]
    (p : W → P) (hp : Measurable p) (future : W → Z) (hf : Measurable future)
    (hsplit : MeasurableEmbedding (fun w => (p w, future w)))
    (η : Kernel W O) [IsMarkovKernel η]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : W × O => (p q.1, past q.2))
      (fun q => future q.1) (ρ ⊗ₘ η)) :
    ∃ κ : Kernel P X, IsMarkovKernel κ ∧
      (fun w => (η.map past) w) =ᵐ[ρ] (fun w => κ (p w)) := by
  let : IsProbabilityMeasure (ρ.map p) := inferInstance
  let : IsProbabilityMeasure (ρ.map future) := inferInstance
  have hbase : IndepFun (fun q : W × O => p q.1)
      (fun q => future q.1) (ρ ⊗ₘ η) := hind.comp measurable_fst measurable_id
  have hlaw := hbase.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  change (ρ ⊗ₘ η).map ((fun w => (p w, future w)) ∘ Prod.fst) =
    ((ρ ⊗ₘ η).map (p ∘ Prod.fst)).prod
      ((ρ ⊗ₘ η).map (future ∘ Prod.fst)) at hlaw
  rw [← Measure.map_map (hp.prodMk hf) measurable_fst,
    ← Measure.map_map hp measurable_fst, ← Measure.map_map hf measurable_fst] at hlaw
  change ((ρ ⊗ₘ η).fst.map (fun w => (p w, future w))) =
    ((ρ ⊗ₘ η).fst.map p).prod ((ρ ⊗ₘ η).fst.map future) at hlaw
  rw [Measure.fst_compProd] at hlaw
  exact KernelCompatibility.exists_past_kernel_of_indep_of_embedding ρ
    (ρ.map p) (ρ.map future) p hp future hf hsplit hlaw η past hpast hind

theorem condExp_joinedPast_left_of_kernel_extension
    (ρ : Measure W) [IsProbabilityMeasure ρ]
    (η : Kernel W O) [IsMarkovKernel η]
    (p : W → P) (hp : Measurable p)
    (past : O → X) (hpast : Measurable past)
    (κ : Kernel P X) [IsMarkovKernel κ]
    (hκ : (fun w => (η.map past) w) =ᵐ[ρ] (fun w => κ (p w)))
    {m : MeasurableSpace (W × O)} (hm : m ≤ mW.prod mO)
    {f : W × O → ℝ} (hf : Integrable f (ρ ⊗ₘ η))
    (hCE : let Q := (ρ ⊗ₘ η) ⊗ₘ
        κ.comap (fun q : W × O => p q.1) (hp.comp measurable_fst)
      Q[(fun z : (W × O) × X => f z.1) | m.prod inferInstance] =ᵐ[Q]
        fun z => (ρ ⊗ₘ η)[f | m] z.1) :
    (ρ ⊗ₘ (η ×ₖ η))[(fun q : W × (O × O) => f (q.1, q.2.1)) |
      m.comap (fun q : W × (O × O) => (q.1, q.2.1)) ⊔
        MeasurableSpace.comap (fun q : W × (O × O) => past q.2.2) inferInstance] =ᵐ[ρ ⊗ₘ (η ×ₖ η)]
      fun q => (ρ ⊗ₘ η)[f | m] (q.1, q.2.1) := by
  let : MeasurableSpace (W × O) := mW.prod mO
  let Q := (ρ ⊗ₘ η) ⊗ₘ κ.comap (fun q : W × O => p q.1) (hp.comp measurable_fst)
  let ψ : W × (O × O) → (W × O) × X := fun q => ((q.1, q.2.1), past q.2.2)
  have hψ : MeasurePreserving ψ (ρ ⊗ₘ (η ×ₖ η)) Q :=
    ⟨by fun_prop, map_onePast ρ η p hp past hpast κ hκ⟩
  have hfst : MeasurePreserving (Prod.fst : (W × O) × X → W × O) Q (ρ ⊗ₘ η) :=
    ⟨measurable_fst, Measure.fst_compProd _ _⟩
  have hprod : m.prod (inferInstance : MeasurableSpace X) ≤
      (inferInstance : MeasurableSpace ((W × O) × X)) := by
    exact sup_le_sup (MeasurableSpace.comap_mono hm) le_rfl
  have hj := condExp_comp_measurePreserving (ρ ⊗ₘ (η ×ₖ η)) Q ψ hψ
    (m.prod inferInstance) hprod (hfst.integrable_comp_of_integrable hf)
  have he := hψ.quasiMeasurePreserving.ae hCE
  have htrans := hj.trans he
  simpa only [MeasurableSpace.prod, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_comp, Function.comp_def, ψ] using htrans

theorem condExp_joinedPast_left
    (ρ : Measure W) [IsProbabilityMeasure ρ]
    (η : Kernel W O) [IsMarkovKernel η]
    (p : W → P) (hp : Measurable p)
    (past : O → X) (hpast : Measurable past)
    (κ : Kernel P X) [IsMarkovKernel κ]
    (hκ : (fun w => (η.map past) w) =ᵐ[ρ] (fun w => κ (p w)))
    {m : MeasurableSpace (W × O)} (hm : m ≤ mW.prod mO)
    (hpM : Measurable[m] (fun q : W × O => p q.1))
    {f : W × O → ℝ} (hf : Integrable f (ρ ⊗ₘ η)) :
    (ρ ⊗ₘ (η ×ₖ η))[(fun q : W × (O × O) => f (q.1, q.2.1)) |
      m.comap (fun q : W × (O × O) => (q.1, q.2.1)) ⊔
        MeasurableSpace.comap (fun q : W × (O × O) => past q.2.2) mX] =ᵐ[ρ ⊗ₘ (η ×ₖ η)]
      fun q => (ρ ⊗ₘ η)[f | m] (q.1, q.2.1) := by
  let : MeasurableSpace (W × O) := mW.prod mO
  apply condExp_joinedPast_left_of_kernel_extension ρ η p hp past hpast κ hκ hm hf
  exact KernelExtensionConditionalExpectation.condExp_fst_compProd hm hpM κ hf

theorem martingale_left
    {I : Type*} [Preorder I]
    (ρ : Measure W) [IsProbabilityMeasure ρ]
    (η : Kernel W O) [IsMarkovKernel η]
    (p : I → W → P) (hp : ∀ t, Measurable (p t))
    (past : I → O → X) (hpast : ∀ t, Measurable (past t))
    (F : Filtration I (mW.prod mO))
    (G : Filtration I (mW.prod (mO.prod mO)))
    (hG : ∀ t, G t =
      (F t).comap (fun q : W × (O × O) => (q.1, q.2.1)) ⊔
        MeasurableSpace.comap (fun q : W × (O × O) => past t q.2.2) mX)
    (hpF : ∀ t, Measurable[F t] (fun q : W × O => p t q.1))
    (hcompatible : ∀ t, ∃ κ : Kernel P X, IsMarkovKernel κ ∧
      (fun w => (η.map (past t)) w) =ᵐ[ρ] fun w => κ (p t w))
    {M : I → W × O → ℝ} (hM : Martingale M F (ρ ⊗ₘ η)) :
    Martingale (fun t (q : W × (O × O)) => M t (q.1, q.2.1)) G (ρ ⊗ₘ (η ×ₖ η)) := by
  have hpair := measurePreserving_conditionalCopy_fst ρ η
  refine ⟨?_, ?_⟩
  · intro t
    apply (hM.stronglyAdapted t).comp_measurable
    rw [hG t]
    exact Measurable.of_comap_le le_sup_left
  · intro s t hst
    obtain ⟨κ, hκ, hcompat⟩ := hcompatible s
    let := hκ
    rw [hG s]
    exact (condExp_joinedPast_left ρ η (p s) (hp s) (past s) (hpast s)
      κ hcompat (F.le s) (hpF s) (hM.integrable t)).trans
        (hpair.quasiMeasurePreserving.ae (hM.condExp_ae_eq hst))

end Problem367.ConditionalCopyImmersion

end

end OAI
