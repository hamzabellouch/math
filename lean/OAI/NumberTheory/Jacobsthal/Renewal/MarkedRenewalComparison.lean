import OAI.NumberTheory.Jacobsthal.Probability.MarkedReturnKernel

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.RegenerationTails NumberTheoryLean.KernelPotential
open NumberTheoryLean.CycleConvolutionLaw NumberTheoryLean.CycleRenewalInputs

instance markedReturn_pow_isMarkovKernel (n : ℕ) : IsMarkovKernel (markedReturnKernel ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel OddCost OddCost); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsMarkovKernel (markedReturnKernel ∘ₖ (markedReturnKernel ^ n))
    infer_instance

lemma markedReturn_cumulative_cost_lintegral (n : ℕ) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y.2 ∂(markedReturnKernel ^ n) z) = ∫⁻ G, H (z.2+G) ∂convPow markedSpacingLaw n := by
  induction n generalizing z with
  | zero =>
    change (∫⁻ y, H y.2 ∂Measure.dirac z) = _
    rw [lintegral_dirac' z (f := fun y : OddCost => H y.2) (hH.comp measurable_snd),convPow_zero,
      lintegral_dirac' 0 (f := fun G : ℝ => H (z.2+G)) (hH.comp (measurable_const.add measurable_id)),add_zero]
  | succ n ih =>
    have hp : markedReturnKernel ^ (n+1) = (markedReturnKernel ^ n) ∘ₖ markedReturnKernel := pow_succ _ _
    rw [hp,Kernel.lintegral_comp _ _ _ (g := fun y : OddCost => H y.2) (hH.comp measurable_snd)]
    let F : ℝ → ℝ≥0∞ := fun t => ∫⁻ G, H (z.2+t+G) ∂convPow markedSpacingLaw n
    have hF : Measurable F := (hH.comp ((measurable_const.add measurable_fst).add measurable_snd)).lintegral_prod_right'
    calc
      _ = ∫⁻ y, F (y.2-z.2) ∂markedReturnKernel z := by
        apply lintegral_congr_ae
        filter_upwards [markedReturn_ae_regeneration z] with y hy
        rw [ih y hy]
        apply lintegral_congr
        intro G
        congr 1
        ring
      _ = ∫⁻ t, F t ∂markedSpacingLaw := markedReturn_increment_integral z hz hF
      _ = _ := by
        rw [convPow_succ',Measure.lintegral_conv (f := fun G : ℝ => H (z.2+G))
          (hH.comp (measurable_const.add measurable_id))]
        apply lintegral_congr
        intro t
        apply lintegral_congr
        intro G
        congr 1
        ring

lemma markedReturn_cumulative_cost_law (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    ((markedReturnKernel ^ n) z).map (fun y => y.2-z.2) = convPow markedSpacingLaw n := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map (g := fun y : OddCost => y.2-z.2) hH (measurable_snd.sub measurable_const),
    markedReturn_cumulative_cost_lintegral n z hz (H := fun G => H (G-z.2))
      (hH.comp (measurable_id.sub measurable_const))]
  simp only [add_sub_cancel_left]

lemma potential_mono_base {B C : Kernel OddCost OddCost} (h : B ≤ C) (K : Kernel OddCost OddCost) :
    potential B K ≤ potential C K := by
  apply potential_le_of_super B K (potential C K)
  calc
    _ ≤ C+(potential C K) ∘ₖ K := fun z => add_le_add (h z) le_rfl
    _ = _ := (potential_unfold C K).symm

lemma markedReturn_potential_le_full :
    potential (Kernel.id : Kernel OddCost OddCost) markedReturnKernel ≤ potential Kernel.id returnLaw := by
  have hsum : cycleBranchKernel false+cycleBranchKernel true=returnLaw := by
    rw [add_comm]
    exact cycleBranch_sum
  have he : potential (Kernel.id : Kernel OddCost OddCost) returnLaw =
      potential (potential Kernel.id (cycleBranchKernel false)) markedReturnKernel := by
    rw [← hsum]
    exact first_capture_decomposition _ _ _
  have hId : (Kernel.id : Kernel OddCost OddCost) ≤ potential Kernel.id (cycleBranchKernel false) := by
    rw [potential_unfold]
    intro z
    exact Measure.le_add_right le_rfl
  exact (potential_mono_base hId markedReturnKernel).trans_eq he.symm

lemma markedReturn_renewal_projection :
    ((potential (Kernel.id : Kernel OddCost OddCost) markedReturnKernel) (regenerationState,0)).map Prod.snd =
      renewalMeasure markedSpacingLaw := by
  rw [potential,Kernel.sum_apply,Measure.map_sum measurable_snd.aemeasurable,renewalMeasure]
  apply congrArg Measure.sum
  funext n
  rw [Kernel.id_comp]
  have he := markedReturn_cumulative_cost_law n (regenerationState,0)
    (by norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,regenerationState])
  simpa only [sub_zero] using he

lemma fullReturn_renewal_projection :
    ((potential (Kernel.id : Kernel OddCost OddCost) returnLaw) (regenerationState,0)).map Prod.snd =
      renewalMeasure cycleCostLaw := by
  rw [← actualArrival_sum_eq_renewal,potential,Kernel.sum_apply,Measure.map_sum measurable_snd.aemeasurable]
  apply congrArg Measure.sum
  funext n
  rw [Kernel.id_comp]
  rfl

lemma marked_renewal_le_full : renewalMeasure markedSpacingLaw ≤ renewalMeasure cycleCostLaw := by
  rw [← markedReturn_renewal_projection,← fullReturn_renewal_projection]
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply measurable_snd hB,Measure.map_apply measurable_snd hB]
  exact markedReturn_potential_le_full (regenerationState,0) _

theorem marked_renewal_cell_bound (ell : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
    renewalMeasure markedSpacingLaw (Icc y (y+ell)) ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC⟩ := cycle_renewal_cell_bound ell
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro y
  exact (marked_renewal_le_full _).trans ((hC y).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
