import OAI.NumberTheory.Jacobsthal.Probability.GeometricCostLaws

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw

noncomputable def cycleBranchKernel (b : Bool) : Kernel OddCost OddCost :=
  (completedMarkedKernel.restrict (measurable_fst (measurableSet_singleton b))).map Prod.snd

instance cycleBranchKernel_isFiniteKernel (b : Bool) : IsFiniteKernel (cycleBranchKernel b) := by
  unfold cycleBranchKernel
  infer_instance

instance cycleBranch_pow_isFiniteKernel (b : Bool) (n : ℕ) : IsFiniteKernel (cycleBranchKernel b ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel OddCost OddCost); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsFiniteKernel (cycleBranchKernel b ∘ₖ (cycleBranchKernel b ^ n))
    infer_instance

noncomputable def branchCostLaw (b : Bool) : Measure ℝ :=
  (sourceCycleLaw.restrict {z | z.1=b}).map sourceCostProjection

lemma branchCostLaw_true : branchCostLaw true = markedCostLaw := rfl

lemma false_mark_set : {z : MarkedOddCost | z.1=false} = sourceMarkSetᶜ := by
  ext z
  cases z.1 <;> simp [sourceMarkSet]

lemma branchCostLaw_false : branchCostLaw false = unmarkedCostLaw := by
  rw [branchCostLaw,false_mark_set]
  rfl

instance branchCostLaw_isFiniteMeasure (b : Bool) : IsFiniteMeasure (branchCostLaw b) := by
  unfold branchCostLaw
  infer_instance

lemma cycleBranch_sum : cycleBranchKernel true+cycleBranchKernel false = returnLaw := by
  ext z : 1
  rw [add_apply]
  unfold cycleBranchKernel
  rw [Kernel.map_apply _ measurable_snd,Kernel.map_apply _ measurable_snd,
    Kernel.restrict_apply,Kernel.restrict_apply]
  change ((completedMarkedKernel z).restrict {y | y.1=true}).map Prod.snd +
    ((completedMarkedKernel z).restrict {y | y.1=false}).map Prod.snd = returnLaw z
  rw [false_mark_set]
  change ((completedMarkedKernel z).restrict sourceMarkSet).map Prod.snd +
    ((completedMarkedKernel z).restrict sourceMarkSetᶜ).map Prod.snd = returnLaw z
  rw [← Measure.map_add _ _ measurable_snd,Measure.restrict_add_restrict_compl sourceMarkSet_measurable,
    completedMarked_forget]

lemma cycleBranch_ae_regeneration (b : Bool) (z : OddCost) :
    ∀ᵐ y ∂cycleBranchKernel b z, y ∈ returnSet := by
  rw [cycleBranchKernel,Kernel.map_apply _ measurable_snd,Kernel.restrict_apply]
  apply (ae_map_iff measurable_snd.aemeasurable returnSet_measurable).mpr
  exact ae_restrict_of_ae (completedMarked_ae_regeneration z)

lemma cycleBranch_increment_integral (b : Bool) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H (y.2-z.2) ∂cycleBranchKernel b z) = ∫⁻ G, H G ∂branchCostLaw b := by
  let F : Bool × ℝ → ℝ≥0∞ := fun x => if x.1=b then H x.2 else 0
  have hF : Measurable F := Measurable.ite (measurable_fst (measurableSet_singleton b))
    (hH.comp measurable_snd) measurable_const
  have hB : MeasurableSet {y : MarkedOddCost | y.1=b} := measurable_fst (measurableSet_singleton b)
  have hleft : (∫⁻ y, H (y.2-z.2) ∂cycleBranchKernel b z) =
      ∫⁻ y, F (y.1,y.2.2-z.2) ∂completedMarkedKernel z := by
    rw [cycleBranchKernel,Kernel.map_apply _ measurable_snd,Kernel.restrict_apply,
      lintegral_map (f := fun y : OddCost => H (y.2-z.2)) (hH.comp (measurable_snd.sub measurable_const)) measurable_snd]
    change (∫⁻ y in {a : MarkedOddCost | a.1=b}, H (y.2.2-z.2) ∂completedMarkedKernel z) = _
    rw [← lintegral_indicator hB]
    apply lintegral_congr
    intro y
    simp [F,Set.indicator_apply]
  have hright : (∫⁻ G, H G ∂branchCostLaw b) = ∫⁻ u, F u ∂jointMarkCostLaw := by
    rw [branchCostLaw,lintegral_map hH sourceCostProjection_measurable,
      ← lintegral_indicator hB,jointMarkCostLaw,lintegral_map hF markCostProjection_measurable]
    apply lintegral_congr
    intro y
    simp [F,sourceCostProjection,markCostProjection,Set.indicator_apply]
  rw [hleft,hright,marked_cycle_increment_integral z hz hF]

lemma cycleBranch_cost_lintegral (b : Bool) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y.2 ∂cycleBranchKernel b z) = ∫⁻ G, H (z.2+G) ∂branchCostLaw b := by
  have he := cycleBranch_increment_integral b z hz
    (H := fun G => H (z.2+G)) (hH.comp (measurable_const.add measurable_id))
  simpa [add_sub_assoc] using he

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw

lemma cycleBranch_mass (b : Bool) (z : OddCost) (hz : z ∈ returnSet) :
    cycleBranchKernel b z univ = branchCostLaw b univ := by
  simpa only [lintegral_one] using cycleBranch_increment_integral b z hz (H := fun _ => 1) measurable_const

lemma cycleBranch_true_mass (z : OddCost) (hz : z ∈ returnSet) :
    cycleBranchKernel true z univ = markProbability := by
  rw [cycleBranch_mass true z hz,branchCostLaw_true,markedCostLaw_mass]

lemma cycleBranch_pow_ae_regeneration (b : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    ∀ᵐ y ∂(cycleBranchKernel b ^ n) z, y ∈ returnSet := by
  cases n with
  | zero =>
    change ∀ᵐ y ∂Measure.dirac z, y ∈ returnSet
    exact (ae_dirac_iff returnSet_measurable).mpr hz
  | succ n =>
    rw [pow_succ']
    change ∀ᵐ y ∂(cycleBranchKernel b ∘ₖ (cycleBranchKernel b ^ n)) z, y ∈ returnSet
    exact Kernel.ae_comp_of_ae_ae returnSet_measurable (Eventually.of_forall (cycleBranch_ae_regeneration b))

lemma branch_cumulative_cost_lintegral (b : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y.2 ∂(cycleBranchKernel b ^ n) z) =
      ∫⁻ G, H (z.2+G) ∂convPow (branchCostLaw b) n := by
  induction n generalizing z with
  | zero =>
    change (∫⁻ y, H y.2 ∂Measure.dirac z) = _
    rw [lintegral_dirac' z (f := fun y : OddCost => H y.2) (hH.comp measurable_snd),convPow_zero,
      lintegral_dirac' 0 (f := fun G : ℝ => H (z.2+G)) (hH.comp (measurable_const.add measurable_id)),add_zero]
  | succ n ih =>
    have hp : cycleBranchKernel b ^ (n+1) = (cycleBranchKernel b ^ n) ∘ₖ cycleBranchKernel b := pow_succ _ _
    rw [hp,Kernel.lintegral_comp _ _ _ (g := fun y : OddCost => H y.2) (hH.comp measurable_snd)]
    let F : ℝ → ℝ≥0∞ := fun t => ∫⁻ G, H (z.2+t+G) ∂convPow (branchCostLaw b) n
    have hF : Measurable F := (hH.comp ((measurable_const.add measurable_fst).add measurable_snd)).lintegral_prod_right'
    calc
      _ = ∫⁻ y, F (y.2-z.2) ∂cycleBranchKernel b z := by
        apply lintegral_congr_ae
        filter_upwards [cycleBranch_ae_regeneration b z] with y hy
        rw [ih y hy]
        apply lintegral_congr
        intro G
        congr 1
        ring
      _ = ∫⁻ t, F t ∂branchCostLaw b := cycleBranch_increment_integral b z hz hF
      _ = _ := by
        rw [convPow_succ',Measure.lintegral_conv (f := fun G : ℝ => H (z.2+G))
          (hH.comp (measurable_const.add measurable_id))]
        apply lintegral_congr
        intro t
        apply lintegral_congr
        intro G
        congr 1
        ring

lemma branch_cumulative_cost_law (b : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    ((cycleBranchKernel b ^ n) z).map (fun y => y.2-z.2) = convPow (branchCostLaw b) n := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map (g := fun y : OddCost => y.2-z.2) hH (measurable_snd.sub measurable_const),
    branch_cumulative_cost_lintegral b n z hz (H := fun G => H (G-z.2))
      (hH.comp (measurable_id.sub measurable_const))]
  simp only [add_sub_cancel_left]

lemma branch_word_ae_regeneration (first rest : Bool) (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂((cycleBranchKernel rest ^ n) ∘ₖ cycleBranchKernel first) z, y ∈ returnSet := by
  apply Kernel.ae_comp_of_ae_ae returnSet_measurable
  filter_upwards [cycleBranch_ae_regeneration first z] with y hy
  exact cycleBranch_pow_ae_regeneration rest n y hy

lemma branch_word_cost_lintegral (first rest : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y.2 ∂((cycleBranchKernel rest ^ n) ∘ₖ cycleBranchKernel first) z) =
      ∫⁻ G, H (z.2+G) ∂(branchCostLaw first ∗ convPow (branchCostLaw rest) n) := by
  rw [Kernel.lintegral_comp _ _ _ (g := fun y : OddCost => H y.2) (hH.comp measurable_snd)]
  let F : ℝ → ℝ≥0∞ := fun t => ∫⁻ G, H (z.2+t+G) ∂convPow (branchCostLaw rest) n
  have hF : Measurable F := (hH.comp ((measurable_const.add measurable_fst).add measurable_snd)).lintegral_prod_right'
  calc
    _ = ∫⁻ y, F (y.2-z.2) ∂cycleBranchKernel first z := by
      apply lintegral_congr_ae
      filter_upwards [cycleBranch_ae_regeneration first z] with y hy
      rw [branch_cumulative_cost_lintegral rest n y hy hH]
      apply lintegral_congr
      intro G
      congr 1
      ring
    _ = ∫⁻ t, F t ∂branchCostLaw first := cycleBranch_increment_integral first z hz hF
    _ = _ := by
      rw [Measure.lintegral_conv (f := fun G : ℝ => H (z.2+G)) (hH.comp (measurable_const.add measurable_id))]
      apply lintegral_congr
      intro t
      apply lintegral_congr
      intro G
      congr 1
      ring

lemma branch_word_cost_law (first rest : Bool) (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    (((cycleBranchKernel rest ^ n) ∘ₖ cycleBranchKernel first) z).map (fun y => y.2-z.2) =
      branchCostLaw first ∗ convPow (branchCostLaw rest) n := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map (g := fun y : OddCost => y.2-z.2) hH (measurable_snd.sub measurable_const),
    branch_word_cost_lintegral first rest n z hz (H := fun G => H (G-z.2))
      (hH.comp (measurable_id.sub measurable_const))]
  simp only [add_sub_cancel_left]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
