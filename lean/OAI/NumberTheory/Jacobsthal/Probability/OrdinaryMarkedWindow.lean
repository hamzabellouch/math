import OAI.NumberTheory.Jacobsthal.Renewal.RawInitialDelay

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma potential_factor_right (B : Kernel α β) (U : Kernel α α) :
    potential B U = B ∘ₖ potential Kernel.id U := by
  simpa only [Kernel.comp_id] using potential_comp_left (Kernel.id : Kernel α α) B U

lemma kernel_middle_power (S H : Kernel α α) (n : ℕ) :
    S ∘ₖ ((H ∘ₖ S)^n) = ((S ∘ₖ H)^n) ∘ₖ S := (mul_pow_mul S H n).symm

lemma potential_exchange (B : Kernel α β) (S H : Kernel α α) :
    potential (B ∘ₖ S) (H ∘ₖ S) = (potential B (S ∘ₖ H)) ∘ₖ S := by
  rw [potential,potential,Kernel.comp_sum_left]
  apply congrArg Kernel.sum
  funext n
  rw [Kernel.comp_assoc,kernel_middle_power,← Kernel.comp_assoc]

theorem potential_denesting (B : Kernel α β) (U H : Kernel α α) :
    potential B (U+H) =
      (potential B ((potential Kernel.id U) ∘ₖ H)) ∘ₖ potential Kernel.id U := by
  rw [first_capture_decomposition,potential_factor_right B U,potential_factor_right H U,potential_exchange]

lemma compose_mono_right_general {K L : Kernel α α} (hKL : K ≤ L) (B : Kernel α β) :
    B ∘ₖ K ≤ B ∘ₖ L := by
  intro x
  apply Measure.le_iff.mpr
  intro S hS
  rw [Kernel.comp_apply' _ _ _ hS,Kernel.comp_apply' _ _ _ hS]
  exact lintegral_mono' (hKL x) le_rfl

lemma potential_mono_step_general {K L : Kernel α α} (hKL : K ≤ L) (B : Kernel α β) :
    potential B K ≤ potential B L := by
  apply potential_le_of_super B K (potential B L)
  calc
    _ ≤ B+(potential B L) ∘ₖ L := fun x => add_le_add le_rfl ((compose_mono_right_general hKL _) x)
    _ = _ := (potential_unfold B L).symm

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.KernelPotential

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

noncomputable def stateFilter {S : Set α} (hS : MeasurableSet S) : Kernel α α := Kernel.id.restrict hS

instance stateFilter_isFiniteKernel {S : Set α} (hS : MeasurableSet S) : IsFiniteKernel (stateFilter hS) := by
  unfold stateFilter
  infer_instance

lemma stateFilter_apply {S : Set α} (hS : MeasurableSet S) (x : α) :
    stateFilter hS x = if x ∈ S then Measure.dirac x else 0 := by
  classical
  rw [stateFilter,Kernel.restrict_apply,Kernel.id_apply,restrict_dirac' hS]

lemma stateFilter_mass {S : Set α} (hS : MeasurableSet S) (x : α) :
    stateFilter hS x univ = if x ∈ S then 1 else 0 := by
  classical
  rw [stateFilter_apply]
  split_ifs <;> simp

lemma stateFilter_output (K : Kernel α β) {S : Set β} (hS : MeasurableSet S) :
    stateFilter hS ∘ₖ K = K.restrict hS := by
  rw [stateFilter,Kernel.comp_restrict,Kernel.id_comp]

lemma stateFilter_input (K : Kernel α β) {S : Set α} (hS : MeasurableSet S) (x : α) :
    (K ∘ₖ stateFilter hS) x = if x ∈ S then K x else 0 := by
  classical
  by_cases hx : x ∈ S
  · rw [ite_eq_left hx]
    ext B hB
    rw [Kernel.comp_apply' _ _ _ hB,stateFilter_apply,ite_eq_left hx,lintegral_dirac' x (K.measurable_coe hB)]
  · rw [ite_eq_right hx]
    ext B hB
    rw [Kernel.comp_apply' _ _ _ hB,stateFilter_apply,ite_eq_right hx,lintegral_zero_measure]
    rfl

lemma stateFilter_mono {S T : Set α} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T) :
    stateFilter hS ≤ stateFilter hT := by
  classical
  intro x
  by_cases hx : x ∈ S
  · rw [stateFilter_apply,stateFilter_apply,ite_eq_left hx,ite_eq_left (hST hx)]
  · rw [stateFilter_apply,ite_eq_right hx]
    exact Measure.zero_le _

instance stateFilter_stopping_isMarkov (R : Kernel α α) [IsMarkovKernel R]
    {S : Set α} (hS : MeasurableSet S) : IsMarkovKernel (stateFilter hS+R ∘ₖ stateFilter hS.compl) := by
  classical
  constructor
  intro x
  constructor
  rw [_root_.add_apply,Measure.add_apply,stateFilter_mass,stateFilter_input]
  by_cases hx : x ∈ S <;> simp [hx]

lemma capturePotential_mass_le_one (B H : Kernel α α) [IsFiniteKernel B] [IsFiniteKernel H]
    [IsMarkovKernel (B+H)] (x : α) : potential B H x univ ≤ 1 := by
  have (n : ℕ) : IsFiniteKernel (H^n) := by
    induction n with
    | zero => change IsFiniteKernel (Kernel.id : Kernel α α); infer_instance
    | succ n ih => rw [pow_succ']; change IsFiniteKernel (H ∘ₖ (H^n)); infer_instance
  have hs (n : ℕ) : (B ∘ₖ (H^n)) x univ+(H^(n+1)) x univ=(H^n) x univ := by
    have hp : H^(n+1)=H ∘ₖ (H^n) := pow_succ' _ _
    calc
      _ = ((B+H) ∘ₖ (H^n)) x univ := by rw [Kernel.comp_add_left,_root_.add_apply,Measure.add_apply,hp]
      _ = _ := by
        rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
        simp only [measure_univ,lintegral_const,one_mul]
  have hf (n : ℕ) : (H^n) x univ+∑ k ∈ Finset.range n, (B ∘ₖ (H^k)) x univ=1 := by
    induction n with
    | zero => change (Measure.dirac x) univ+0=1; simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        _ = (∑ k ∈ Finset.range n, (B ∘ₖ (H^k)) x univ)+
            ((B ∘ₖ (H^n)) x univ+(H^(n+1)) x univ) := by ac_rfl
        _ = _ := by rw [hs]; simpa only [add_comm] using ih
  rw [potential,Kernel.sum_apply' _ _ MeasurableSet.univ,ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  calc
    _ ≤ (H^n) x univ+∑ k ∈ Finset.range n, (B ∘ₖ (H^k)) x univ := le_add_left le_rfl
    _ = 1 := hf n

lemma currentHit_outside (R : Kernel α α) {S : Set α} (hS : MeasurableSet S) (x : α) (hx : x ∉ S) :
    potential (stateFilter hS) (R ∘ₖ stateFilter hS.compl) x =
      (potential (stateFilter hS) (R ∘ₖ stateFilter hS.compl) ∘ₖ R) x := by
  classical
  conv_lhs =>
    rw [potential_unfold,_root_.add_apply,stateFilter_apply,ite_eq_right hx,
      ← Kernel.comp_assoc,stateFilter_input,ite_eq_left (show x ∈ Sᶜ from hx),zero_add]

lemma currentHit_inside (R : Kernel α α) {S : Set α} (hS : MeasurableSet S) (x : α) (hx : x ∈ S) :
    1 ≤ potential (stateFilter hS) (R ∘ₖ stateFilter hS.compl) x univ := by
  rw [potential_unfold,_root_.add_apply,Measure.add_apply,stateFilter_mass,ite_eq_left hx]
  exact le_add_right le_rfl

theorem restricted_crossing_le_current_hit (R : Kernel α α) {S T : Set α}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hTS : T ⊆ Sᶜ) (x : α) (hx : x ∈ T) :
    potential (R.restrict hS) (R.restrict hT) x univ ≤
      potential (stateFilter hS) (R ∘ₖ stateFilter hS.compl) x univ := by
  rw [← stateFilter_output R hS,← stateFilter_output R hT,potential_exchange]
  have hK : R ∘ₖ stateFilter hT ≤ R ∘ₖ stateFilter hS.compl :=
    compose_mono_right_general (stateFilter_mono hT hS.compl hTS) R
  have hP := potential_mono_step_general hK (stateFilter hS)
  have he := currentHit_outside R hS x (hTS hx)
  exact ((compose_mono_left hP R) x univ).trans_eq (congrArg (fun μ : Measure α => μ univ) he.symm)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.KernelPotential

lemma cycleBranch_mass_partition (z : OddCost) :
    cycleBranchKernel true z univ+cycleBranchKernel false z univ=1 := by
  rw [← Measure.add_apply,← _root_.add_apply,cycleBranch_sum]
  exact measure_univ

lemma nextMarkWeight_le_one (z : OddCost) : nextMarkWeight z ≤ 1 := by
  change cycleBranchKernel true z univ ≤ 1
  calc
    _ ≤ cycleBranchKernel true z univ+cycleBranchKernel false z univ := le_add_right le_rfl
    _ = 1 := cycleBranch_mass_partition z

noncomputable def markInputWeightKernel : Kernel OddCost OddCost :=
  Kernel.id.withDensity (fun _ z => nextMarkWeight z)

instance markInputWeightKernel_isFiniteKernel : IsFiniteKernel markInputWeightKernel := by
  apply Kernel.isFiniteKernel_withDensity_of_bounded _ (B := 1) (by simp)
  exact fun _ z => nextMarkWeight_le_one z

lemma markInputWeightKernel_apply (z : OddCost) :
    markInputWeightKernel z=nextMarkWeight z • Measure.dirac z := by
  rw [markInputWeightKernel,Kernel.withDensity_apply _ (f := fun _ z : OddCost => nextMarkWeight z)
    (nextMarkWeight_measurable.comp measurable_snd),Kernel.id_apply,dirac_withDensity' nextMarkWeight_measurable]

noncomputable def ordinaryCostWindow (v H : ℝ) : Set OddCost := Prod.snd ⁻¹' Icc v (v+H)

lemma ordinaryCostWindow_measurable (v H : ℝ) : MeasurableSet (ordinaryCostWindow v H) :=
  measurableSet_Icc.preimage measurable_snd

noncomputable def ordinaryWindowCapture (v H : ℝ) : Kernel OddCost OddCost :=
  markInputWeightKernel.restrict (ordinaryCostWindow_measurable v H)

noncomputable def ordinaryWindowContinue (v H : ℝ) : Kernel OddCost OddCost :=
  cycleBranchKernel false+cycleBranchKernel true ∘ₖ stateFilter (ordinaryCostWindow_measurable v H).compl

instance ordinaryWindowCapture_isFiniteKernel (v H : ℝ) : IsFiniteKernel (ordinaryWindowCapture v H) := by
  unfold ordinaryWindowCapture
  infer_instance

instance ordinaryWindowContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (ordinaryWindowContinue v H) := by
  unfold ordinaryWindowContinue
  infer_instance

lemma ordinaryWindowCapture_mass (v H : ℝ) (z : OddCost) :
    ordinaryWindowCapture v H z univ = if z ∈ ordinaryCostWindow v H then nextMarkWeight z else 0 := by
  rw [ordinaryWindowCapture,Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter,
    markInputWeightKernel_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply' z (ordinaryCostWindow_measurable v H)]
  split_ifs <;> simp_all

instance ordinaryWindow_stop_isMarkov (v H : ℝ) :
    IsMarkovKernel (ordinaryWindowCapture v H+ordinaryWindowContinue v H) := by
  constructor
  intro z
  constructor
  rw [_root_.add_apply,Measure.add_apply,ordinaryWindowCapture_mass,ordinaryWindowContinue,
    _root_.add_apply,Measure.add_apply,stateFilter_input]
  by_cases hz : z ∈ ordinaryCostWindow v H
  · simp only [hz,ite_true,mem_compl_iff,not_true_eq_false,ite_false,Measure.coe_zero,Pi.zero_apply,add_zero]
    exact cycleBranch_mass_partition z
  · simp only [hz,ite_false,mem_compl_iff,not_false_eq_true,ite_true,zero_add]
    simpa only [nextMarkWeight,add_comm] using cycleBranch_mass_partition z

noncomputable def ordinaryMarkedHit (v H : ℝ) : Kernel OddCost OddCost :=
  potential (ordinaryWindowCapture v H) (ordinaryWindowContinue v H)

lemma ordinaryMarkedHit_mass_le_one (v H : ℝ) (z : OddCost) : ordinaryMarkedHit v H z univ ≤ 1 :=
  capturePotential_mass_le_one _ _ z

noncomputable def unmarkedStar : Kernel OddCost OddCost := potential Kernel.id (cycleBranchKernel false)

instance unmarkedStar_isSFiniteKernel : IsSFiniteKernel unmarkedStar := by unfold unmarkedStar; infer_instance

lemma rawBeginning_unmarkedStar : rawBeginningKernel = unmarkedStar ∘ₖ cycleBranchKernel true := by
  rw [unmarkedStar,potential,Kernel.comp_sum_left,rawBeginningKernel]
  apply congrArg Kernel.sum
  funext n
  rw [Kernel.id_comp]

theorem ordinaryMarkedHit_denested (v H : ℝ) :
    ordinaryMarkedHit v H =
      (potential (ordinaryWindowCapture v H)
        (rawBeginningKernel ∘ₖ stateFilter (ordinaryCostWindow_measurable v H).compl)) ∘ₖ unmarkedStar := by
  rw [ordinaryMarkedHit,ordinaryWindowContinue,rawBeginning_unmarkedStar,Kernel.comp_assoc]
  exact potential_denesting _ _ _

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
