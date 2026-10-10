import OAI.NumberTheory.Jacobsthal.Renewal.MarkedCycleWords

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.RegenerationTails

noncomputable def nextMarkWeight (z : OddCost) : ℝ≥0∞ := cycleBranchKernel true z univ

lemma nextMarkWeight_measurable : Measurable nextMarkWeight :=
  (cycleBranchKernel true).measurable_coe MeasurableSet.univ

lemma markProbability_ne_top : markProbability ≠ ∞ :=
  (lt_trans markProbability_lt_one (by simp)).ne

noncomputable def actualWaitingTerm (n : ℕ) (z : OddCost) : Measure ℝ :=
  (((cycleBranchKernel false ^ n) z).withDensity nextMarkWeight).map (fun y => y.2-z.2)

noncomputable def actualSpacingTerm (n : ℕ) (z : OddCost) : Measure ℝ :=
  markProbability⁻¹ •
    ((((cycleBranchKernel false ^ n) ∘ₖ cycleBranchKernel true) z).withDensity nextMarkWeight).map
      (fun y => y.2-z.2)

lemma actualWaitingTerm_eq (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    actualWaitingTerm n z = markProbability • convPow unmarkedCostLaw n := by
  have hw : nextMarkWeight =ᵐ[(cycleBranchKernel false ^ n) z] fun _ => markProbability := by
    filter_upwards [cycleBranch_pow_ae_regeneration false n z hz] with y hy
    exact cycleBranch_true_mass y hy
  have hmap : Measurable (fun y : OddCost => y.2-z.2) := measurable_snd.sub measurable_const
  rw [actualWaitingTerm,withDensity_congr_ae hw,withDensity_const,Measure.map_smul _ hmap.aemeasurable,
    branch_cumulative_cost_law false n z hz,branchCostLaw_false]

lemma actualSpacingTerm_eq (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    actualSpacingTerm n z = markedCostLaw ∗ convPow unmarkedCostLaw n := by
  have hw : nextMarkWeight =ᵐ[((cycleBranchKernel false ^ n) ∘ₖ cycleBranchKernel true) z]
      fun _ => markProbability := by
    filter_upwards [branch_word_ae_regeneration true false n z] with y hy
    exact cycleBranch_true_mass y hy
  have hmap : Measurable (fun y : OddCost => y.2-z.2) := measurable_snd.sub measurable_const
  rw [actualSpacingTerm,withDensity_congr_ae hw,withDensity_const,Measure.map_smul _ hmap.aemeasurable,smul_smul,
    ENNReal.inv_mul_cancel markProbability_pos.ne' markProbability_ne_top,one_smul,
    branch_word_cost_law true false n z hz,branchCostLaw_true,branchCostLaw_false]

noncomputable def actualWaitingLaw (z : OddCost) : Measure ℝ := Measure.sum (fun n => actualWaitingTerm n z)
noncomputable def actualSpacingLaw (z : OddCost) : Measure ℝ := Measure.sum (fun n => actualSpacingTerm n z)

lemma conv_sum_right (μ : Measure ℝ) (ν : ℕ → Measure ℝ) [∀ n, SFinite (ν n)] :
    μ ∗ Measure.sum ν = Measure.sum (fun n => μ ∗ ν n) := by
  unfold Measure.conv
  rw [Measure.prod_sum_right,Measure.map_sum measurable_add.aemeasurable]

lemma actualWaitingLaw_eq (z : OddCost) (hz : z ∈ returnSet) :
    actualWaitingLaw z = markProbability • unmarkedPotential := by
  ext B hB
  rw [actualWaitingLaw,Measure.sum_apply _ hB]
  simp_rw [actualWaitingTerm_eq _ z hz,Measure.smul_apply,smul_eq_mul]
  rw [unmarkedPotential,renewalMeasure,Measure.sum_apply _ hB,ENNReal.tsum_mul_left]

lemma actualSpacingLaw_eq (z : OddCost) (hz : z ∈ returnSet) :
    actualSpacingLaw z = geometricMarkedCostLaw := by
  rw [actualSpacingLaw,geometricMarkedCostLaw,unmarkedPotential,renewalMeasure,conv_sum_right]
  apply congrArg Measure.sum
  funext n
  exact actualSpacingTerm_eq n z hz

lemma actualWaitingLaw_mass (z : OddCost) (hz : z ∈ returnSet) : actualWaitingLaw z univ = 1 := by
  rw [actualWaitingLaw_eq z hz,Measure.smul_apply,smul_eq_mul,unmarkedPotential_mass]
  exact ENNReal.mul_inv_cancel markProbability_pos.ne' markProbability_ne_top

lemma actualSpacingLaw_mass (z : OddCost) (hz : z ∈ returnSet) : actualSpacingLaw z univ = 1 := by
  rw [actualSpacingLaw_eq z hz]
  exact measure_univ

noncomputable def firstMarkWaitingLaw : Measure ℝ := actualWaitingLaw (regenerationState,0)
noncomputable def markedSpacingLaw : Measure ℝ := actualSpacingLaw (regenerationState,0)

instance firstMarkWaitingLaw_isProbabilityMeasure : IsProbabilityMeasure firstMarkWaitingLaw :=
  ⟨actualWaitingLaw_mass _ (by norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,regenerationState])⟩

instance markedSpacingLaw_isProbabilityMeasure : IsProbabilityMeasure markedSpacingLaw :=
  ⟨actualSpacingLaw_mass _ (by norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,regenerationState])⟩

lemma markedSpacingLaw_eq : markedSpacingLaw = geometricMarkedCostLaw :=
  actualSpacingLaw_eq _ (by norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,regenerationState])

lemma markedSpacing_exponential_moment : ∃ eta : ℝ, 0 < eta ∧ costTransform markedSpacingLaw eta < ∞ := by
  rw [markedSpacingLaw_eq]
  exact geometricMarked_exponential_moment

lemma markedSpacing_cost_lower : ∀ᵐ G ∂markedSpacingLaw, Real.log (4/3) ≤ G := by
  rw [markedSpacingLaw_eq]
  exact geometricMarked_cost_lower

lemma firstMarkWaiting_costTransform (eta : ℝ) : costTransform firstMarkWaitingLaw eta =
    markProbability*(1-costTransform unmarkedCostLaw eta)⁻¹ := by
  rw [firstMarkWaitingLaw,actualWaitingLaw_eq _ (by norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,regenerationState])]
  unfold costTransform
  rw [lintegral_smul_measure]
  change markProbability*costTransform unmarkedPotential eta = _
  rw [unmarkedPotential,renewal_costTransform]
  rfl

lemma marked_waiting_common_exponential_moment : ∃ eta : ℝ, 0 < eta ∧
    costTransform firstMarkWaitingLaw eta < ∞ ∧ costTransform markedSpacingLaw eta < ∞ := by
  obtain ⟨eta,heta,hU,hM⟩ := exists_subcritical_unmarked_transform
  have hi : (1-costTransform unmarkedCostLaw eta)⁻¹ < ∞ :=
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hU).ne')
  refine ⟨eta,heta,?_,?_⟩
  · rw [firstMarkWaiting_costTransform]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr markProbability_ne_top) hi
  · rw [markedSpacingLaw_eq,geometricMarked_costTransform]
    exact ENNReal.mul_lt_top hM hi

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.KernelPotential

lemma capture_word_cost_lintegral (n : ℕ) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y.2 ∂(cycleBranchKernel true ∘ₖ (cycleBranchKernel false ^ n)) z) =
      ∫⁻ G, H (z.2+G) ∂(convPow unmarkedCostLaw n ∗ markedCostLaw) := by
  rw [Kernel.lintegral_comp _ _ _ (g := fun y : OddCost => H y.2) (hH.comp measurable_snd)]
  let F : ℝ → ℝ≥0∞ := fun t => ∫⁻ G, H (t+G) ∂markedCostLaw
  have hF : Measurable F := (hH.comp measurable_add).lintegral_prod_right'
  calc
    _ = ∫⁻ y, F y.2 ∂(cycleBranchKernel false ^ n) z := by
      apply lintegral_congr_ae
      filter_upwards [cycleBranch_pow_ae_regeneration false n z hz] with y hy
      rw [cycleBranch_cost_lintegral true y hy hH,branchCostLaw_true]
    _ = ∫⁻ S, F (z.2+S) ∂convPow unmarkedCostLaw n := by
      rw [branch_cumulative_cost_lintegral false n z hz hF,branchCostLaw_false]
    _ = _ := by
      rw [Measure.lintegral_conv (f := fun G : ℝ => H (z.2+G)) (hH.comp (measurable_const.add measurable_id))]
      apply lintegral_congr
      intro S
      apply lintegral_congr
      intro G
      congr 1
      ring

noncomputable def markedReturnKernel : Kernel OddCost OddCost :=
  potential (cycleBranchKernel true) (cycleBranchKernel false)

instance markedReturnKernel_isSFiniteKernel : IsSFiniteKernel markedReturnKernel := by
  unfold markedReturnKernel
  infer_instance

lemma markedReturn_cost_law (z : OddCost) (hz : z ∈ returnSet) :
    (markedReturnKernel z).map (fun y => y.2-z.2) = markedSpacingLaw := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map (g := fun y : OddCost => y.2-z.2) hH (measurable_snd.sub measurable_const),
    markedReturnKernel,potential,Kernel.sum_apply,lintegral_sum_measure,
    markedSpacingLaw_eq,geometricMarkedCostLaw,unmarkedPotential,renewalMeasure,conv_sum_right,
    lintegral_sum_measure]
  apply tsum_congr
  intro n
  have he := capture_word_cost_lintegral n z hz (H := fun G => H (G-z.2))
    (hH.comp (measurable_id.sub measurable_const))
  rw [Measure.conv_comm] at he
  simpa only [add_sub_cancel_left] using he

lemma markedReturn_mass_of_regeneration (z : OddCost) (hz : z ∈ returnSet) :
    markedReturnKernel z univ = 1 := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) (markedReturn_cost_law z hz)
  rw [Measure.map_apply (f := fun y : OddCost => y.2-z.2) (measurable_snd.sub measurable_const) MeasurableSet.univ,preimage_univ] at he
  exact he.trans measure_univ

lemma markedReturn_unfold : markedReturnKernel = cycleBranchKernel true+
    markedReturnKernel ∘ₖ cycleBranchKernel false := potential_unfold _ _

instance markedReturnKernel_isMarkovKernel : IsMarkovKernel markedReturnKernel := by
  constructor
  intro z
  constructor
  rw [markedReturn_unfold,add_apply,Measure.add_apply,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  have hi : (∫⁻ y, markedReturnKernel y univ ∂cycleBranchKernel false z) = cycleBranchKernel false z univ := by
    calc
      _ = ∫⁻ _y, (1:ℝ≥0∞) ∂cycleBranchKernel false z := by
        apply lintegral_congr_ae
        filter_upwards [cycleBranch_ae_regeneration false z] with y hy
        exact markedReturn_mass_of_regeneration y hy
      _ = _ := lintegral_one
  rw [hi]
  have he := congrArg (fun K : Kernel OddCost OddCost => K z univ) cycleBranch_sum
  simpa only [add_apply,Measure.add_apply,measure_univ] using he

lemma markedReturn_ae_regeneration (z : OddCost) : ∀ᵐ y ∂markedReturnKernel z, y ∈ returnSet := by
  rw [markedReturnKernel,potential,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  exact Kernel.ae_comp_of_ae_ae returnSet_measurable
    (Eventually.of_forall (cycleBranch_ae_regeneration true))

lemma markedReturn_increment_integral (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H (y.2-z.2) ∂markedReturnKernel z) = ∫⁻ G, H G ∂markedSpacingLaw := by
  rw [← markedReturn_cost_law z hz,lintegral_map (g := fun y : OddCost => y.2-z.2) hH (measurable_snd.sub measurable_const)]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
