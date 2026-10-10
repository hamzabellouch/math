import OAI.NumberTheory.Jacobsthal.Renewal.MarkedRenewalComparison

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw

noncomputable def rawBeginningKernel : Kernel OddCost OddCost :=
  Kernel.sum (fun n : ℕ => (cycleBranchKernel false ^ n) ∘ₖ cycleBranchKernel true)

instance rawBeginningKernel_isSFiniteKernel : IsSFiniteKernel rawBeginningKernel := by
  unfold rawBeginningKernel
  infer_instance

lemma rawBeginning_ae_regeneration (z : OddCost) : ∀ᵐ y ∂rawBeginningKernel z, y ∈ returnSet := by
  rw [rawBeginningKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  exact branch_word_ae_regeneration true false n z

lemma rawBeginning_project_actual (z : OddCost) (hz : z ∈ returnSet) :
    (rawBeginningKernel z).map (fun y => y.2-z.2) = actualSpacingLaw z := by
  rw [rawBeginningKernel,Kernel.sum_apply,
    Measure.map_sum (f := fun y : OddCost => y.2-z.2) (measurable_snd.sub measurable_const).aemeasurable,actualSpacingLaw]
  apply congrArg Measure.sum
  funext n
  rw [actualSpacingTerm_eq n z hz,branch_word_cost_law true false n z hz,
    branchCostLaw_true,branchCostLaw_false]

lemma rawBeginning_cost_law (z : OddCost) (hz : z ∈ returnSet) :
    (rawBeginningKernel z).map (fun y => y.2-z.2) = markedSpacingLaw := by
  rw [rawBeginning_project_actual z hz,actualSpacingLaw_eq z hz,markedSpacingLaw_eq]

lemma rawBeginning_mass (z : OddCost) (hz : z ∈ returnSet) : rawBeginningKernel z univ = 1 := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) (rawBeginning_cost_law z hz)
  rw [Measure.map_apply (f := fun y : OddCost => y.2-z.2)
    (measurable_snd.sub measurable_const) MeasurableSet.univ,preimage_univ] at he
  exact he.trans measure_univ

abbrev RegCost := {z : OddCost // z ∈ returnSet}

noncomputable def beginningDomainKernel : Kernel RegCost OddCost :=
  rawBeginningKernel.comap Subtype.val measurable_subtype_coe

instance beginningDomainKernel_isMarkovKernel : IsMarkovKernel beginningDomainKernel := by
  constructor
  intro z
  constructor
  rw [beginningDomainKernel,Kernel.comap_apply]
  exact rawBeginning_mass z.1 z.2

noncomputable def markedBeginningKernel : Kernel RegCost RegCost :=
  beginningDomainKernel.comapRight (MeasurableEmbedding.subtype_coe returnSet_measurable)

instance markedBeginningKernel_isMarkovKernel : IsMarkovKernel markedBeginningKernel := by
  apply Kernel.IsMarkovKernel.comapRight
  intro z
  have hae : ∀ᵐ y ∂beginningDomainKernel z, y ∈ returnSet := by
    rw [beginningDomainKernel,Kernel.comap_apply]
    exact rawBeginning_ae_regeneration z.1
  have he := (ae_mem_iff_measure_eq (μ := beginningDomainKernel z)
    returnSet_measurable.nullMeasurableSet).mp hae
  rw [measure_univ] at he
  convert! he using 1
  congr 1
  ext y
  simp

lemma markedBeginning_map_state (z : RegCost) :
    (markedBeginningKernel z).map (Subtype.val : RegCost → OddCost) = rawBeginningKernel z.1 := by
  calc
    _ = (rawBeginningKernel z.1).restrict returnSet := by
      change (((rawBeginningKernel z.1).comap (Subtype.val : RegCost → OddCost)).map Subtype.val) = _
      exact map_comap_subtype_coe (μ := rawBeginningKernel z.1) returnSet_measurable
    _ = _ := Measure.restrict_eq_self_of_ae_mem (rawBeginning_ae_regeneration z.1)

def beginningCost (z : RegCost) : ℝ := z.1.2

lemma beginningCost_measurable : Measurable beginningCost :=
  measurable_snd.comp measurable_subtype_coe

lemma markedBeginning_increment_law (z : RegCost) :
    (markedBeginningKernel z).map (fun y => beginningCost y-beginningCost z) = markedSpacingLaw := by
  calc
    _ = ((markedBeginningKernel z).map (Subtype.val : RegCost → OddCost)).map (fun y => y.2-z.1.2) :=
      (Measure.map_map (measurable_snd.sub measurable_const) measurable_subtype_coe).symm
    _ = (rawBeginningKernel z.1).map (fun y => y.2-z.1.2) := by rw [markedBeginning_map_state]
    _ = _ := rawBeginning_cost_law z.1 z.2

noncomputable def markedClockKernel : Kernel ℝ ℝ :=
  (Kernel.id ×ₖ Kernel.const ℝ markedSpacingLaw).map (fun x : ℝ × ℝ => x.1+x.2)

instance markedClockKernel_isMarkovKernel : IsMarkovKernel markedClockKernel :=
  Kernel.IsMarkovKernel.map _ measurable_add

lemma markedClockKernel_apply (x : ℝ) : markedClockKernel x = markedSpacingLaw.map (fun G => x+G) := by
  ext B hB
  rw [markedClockKernel,Kernel.map_apply' _ measurable_add _ hB,
    Kernel.prod_apply' _ _ _ (measurable_add hB),Kernel.id_apply,lintegral_dirac']
  · rw [Measure.map_apply (f := fun G : ℝ => x+G) (measurable_const.add measurable_id) hB]
    rfl
  · exact measurable_measure_prodMk_left (measurable_add hB)

lemma markedBeginning_cost_kernel_link :
    markedBeginningKernel.map beginningCost = markedClockKernel.comap beginningCost beginningCost_measurable := by
  ext z : 1
  rw [Kernel.map_apply _ beginningCost_measurable,Kernel.comap_apply,markedClockKernel_apply]
  calc
    _ = ((markedBeginningKernel z).map (fun y => beginningCost y-beginningCost z)).map
        (fun G => beginningCost z+G) := by
      rw [Measure.map_map (f := fun y : RegCost => beginningCost y-beginningCost z)
        (g := fun G : ℝ => beginningCost z+G) (measurable_const.add measurable_id)
        (beginningCost_measurable.sub measurable_const)]
      congr 1
      funext y
      simp [Function.comp_apply]
    _ = _ := by rw [markedBeginning_increment_law]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
