import Mathlib.Data.List.OfFn
import OAI.NumberTheory.Jacobsthal.Paths.WindowHitWords

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess

noncomputable def allowedCycleInputs (b : Bool) (v H : ℝ) : Set OddCost :=
  Prod.snd ⁻¹' allowedCycleCosts b v H

lemma allowedCycleInputs_measurable (b : Bool) (v H : ℝ) : MeasurableSet (allowedCycleInputs b v H) :=
  (allowedCycleCosts_measurable b v H).preimage measurable_snd

noncomputable def permittedCycleBranch (b : Bool) (v H : ℝ) : Kernel OddCost OddCost :=
  cycleBranchKernel b ∘ₖ stateFilter (allowedCycleInputs_measurable b v H)

instance permittedCycleBranch_isFiniteKernel (b : Bool) (v H : ℝ) : IsFiniteKernel (permittedCycleBranch b v H) := by
  unfold permittedCycleBranch
  infer_instance

lemma permittedCycleBranch_false (v H : ℝ) : permittedCycleBranch false v H=cycleBranchKernel false := by
  ext z : 1
  rw [permittedCycleBranch,stateFilter_input]
  simp [allowedCycleInputs,allowedCycleCosts]

lemma permittedCycleBranch_true (v H : ℝ) :
    permittedCycleBranch true v H=cycleBranchKernel true ∘ₖ stateFilter (ordinaryCostWindow_measurable v H).compl := rfl

lemma permittedCycleBranch_sum (v H : ℝ) : (∑ b : Bool, permittedCycleBranch b v H)=ordinaryWindowContinue v H := by
  rw [Fintype.sum_bool,permittedCycleBranch_false,permittedCycleBranch_true,ordinaryWindowContinue,add_comm]

noncomputable def sourceHitWordKernel : List Bool → ℝ → ℝ → Kernel OddCost OddCost
  | [], v, H => ordinaryWindowCapture v H
  | b::w, v, H => sourceHitWordKernel w v H ∘ₖ permittedCycleBranch b v H

instance sourceHitWordKernel_isFiniteKernel (w : List Bool) (v H : ℝ) : IsFiniteKernel (sourceHitWordKernel w v H) := by
  induction w with
  | nil => change IsFiniteKernel (ordinaryWindowCapture v H); infer_instance
  | cons b w ih => rw [sourceHitWordKernel]; infer_instance

lemma sourceHitWordKernel_mass (w : List Bool) (v H : ℝ) : ∀ z,
    sourceHitWordMass w v H z=sourceHitWordKernel w v H z univ := by
  induction w with
  | nil => intro z; exact sourceHitWordMass_nil v H z
  | cons b w ih =>
    intro z
    rw [sourceHitWordMass_cons,sourceHitWordKernel,permittedCycleBranch,← Kernel.comp_assoc,stateFilter_input]
    change (if z.2 ∈ allowedCycleCosts b v H then ∫⁻ y, sourceHitWordMass w v H y ∂cycleBranchKernel b z else 0) =
      (if z.2 ∈ allowedCycleCosts b v H then (sourceHitWordKernel w v H ∘ₖ cycleBranchKernel b) z else 0) univ
    by_cases hz : z.2 ∈ allowedCycleCosts b v H
    · rw [ite_eq_left hz,ite_eq_left hz,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
      exact lintegral_congr ih
    · simp [hz]

lemma kernel_comp_finset_sum_left {ι α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (s : Finset ι) (K : ι → Kernel α β) (D : Kernel γ α) :
    (∑ i ∈ s, K i) ∘ₖ D = ∑ i ∈ s, K i ∘ₖ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Kernel.comp_add_left,ih]

lemma kernel_comp_finset_sum_right {ι α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (s : Finset ι) (K : Kernel β γ) (D : ι → Kernel α β) :
    K ∘ₖ (∑ i ∈ s, D i) = ∑ i ∈ s, K ∘ₖ D i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Kernel.comp_add_right,ih]

theorem sourceHitWordKernel_sum_length (v H : ℝ) (n : ℕ) :
    (∑ f : Fin n → Bool, sourceHitWordKernel (List.ofFn f) v H) =
      ordinaryWindowCapture v H ∘ₖ ((ordinaryWindowContinue v H)^n) := by
  induction n with
  | zero =>
    simp [List.ofFn_zero,sourceHitWordKernel]
    exact (Kernel.comp_id _).symm
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp
      (fun f => sourceHitWordKernel (List.ofFn f) v H)]
    simp only [Fintype.sum_prod_type]
    change (∑ b : Bool, ∑ f : Fin n → Bool, sourceHitWordKernel (List.ofFn (Fin.cons b f)) v H) = _
    simp_rw [List.ofFn_cons,sourceHitWordKernel]
    simp_rw [← kernel_comp_finset_sum_left,ih]
    rw [← kernel_comp_finset_sum_right,permittedCycleBranch_sum,pow_succ]
    exact Kernel.comp_assoc _ _ _

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.PairedCostGrouping
open NumberTheoryLean.KernelPotential

abbrev RawMarkedHitTrace (a : ℕ) :=
  Σ n : ℕ, Σ f : Fin n → Bool, RawCycleWordTrace a (List.ofFn f++[true]).length

def packRawMarkedHitTrace (a n : ℕ) (f : Fin n → Bool)
    (t : RawCycleWordTrace a (List.ofFn f++[true]).length) : RawMarkedHitTrace a :=
  @Sigma.mk ℕ (fun m => Σ g : Fin m → Bool, RawCycleWordTrace a (List.ofFn g++[true]).length) n
    (@Sigma.mk (Fin n → Bool) (fun g => RawCycleWordTrace a (List.ofFn g++[true]).length) f t)

lemma packRawMarkedHitTrace_measurable (a n : ℕ) (f : Fin n → Bool) :
    Measurable (packRawMarkedHitTrace a n f) :=
  (measurableSigmaMk (X := fun m : ℕ => Σ g : Fin m → Bool, RawCycleWordTrace a (List.ofFn g++[true]).length) n).comp
    (measurableSigmaMk (X := fun g : Fin n → Bool => RawCycleWordTrace a (List.ofFn g++[true]).length) f)

noncomputable def rawMarkedFirstHitKernel (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawMarkedHitTrace a) :=
  Kernel.sum (fun n : ℕ => Kernel.sum (fun f : Fin n → Bool =>
    (rawHitWordKernel a (List.ofFn f) v H).map (packRawMarkedHitTrace a n f)))

instance rawMarkedFirstHitKernel_isSFiniteKernel (a : ℕ) (v H : ℝ) : IsSFiniteKernel (rawMarkedFirstHitKernel a v H) := by
  unfold rawMarkedFirstHitKernel
  infer_instance

theorem rawMarkedFirstHit_mass (a : ℕ) (v H : ℝ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    rawMarkedFirstHitKernel a v H h univ=ordinaryMarkedHit v H z univ := by
  rw [rawMarkedFirstHitKernel,Kernel.sum_apply' _ _ MeasurableSet.univ,
    ordinaryMarkedHit,potential,Kernel.sum_apply' _ _ MeasurableSet.univ]
  apply tsum_congr
  intro n
  rw [Kernel.sum_apply' _ _ MeasurableSet.univ]
  calc
    _ = ∑' f : Fin n → Bool, sourceHitWordKernel (List.ofFn f) v H z univ := by
      apply tsum_congr
      intro f
      rw [Kernel.map_apply' _ (packRawMarkedHitTrace_measurable a n f) _ MeasurableSet.univ,
        preimage_univ,rawHitWord_mass a (List.ofFn f) v H h z hz,sourceHitWordKernel_mass]
    _ = (∑ f : Fin n → Bool, sourceHitWordKernel (List.ofFn f) v H) z univ := by
      rw [tsum_fintype,Kernel.finsetSum_apply']
    _ = _ := by rw [sourceHitWordKernel_sum_length]

noncomputable def rawMarkedHitEvent (a : ℕ) (v H : ℝ) : Set (RawMarkedHitTrace a) :=
  {r | rawCycleWordSignature a (List.ofFn r.2.1++[true]).length r.2.2 ∈ hitWordEvent (List.ofFn r.2.1) v H}

lemma rawMarkedHitEvent_measurable (a : ℕ) (v H : ℝ) : MeasurableSet (rawMarkedHitEvent a v H) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro f
  exact (hitWordEvent_measurable (List.ofFn f) v H).preimage (rawCycleWordSignature_measurable _ a)

theorem rawMarkedFirstHit_ae_event (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    ∀ᵐ r ∂rawMarkedFirstHitKernel a v H h, r ∈ rawMarkedHitEvent a v H := by
  rw [rawMarkedFirstHitKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.sum_apply,Measure.ae_sum_iff]
  intro f
  rw [Kernel.map_apply _ (packRawMarkedHitTrace_measurable a n f)]
  apply (ae_map_iff (packRawMarkedHitTrace_measurable a n f).aemeasurable (rawMarkedHitEvent_measurable a v H)).mpr
  rw [rawHitWordKernel,Kernel.restrict_apply]
  exact ae_restrict_mem ((hitWordEvent_measurable (List.ofFn f) v H).preimage (rawCycleWordSignature_measurable _ a))

noncomputable def rawRegMarkedFirstHitKernel (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawMarkedHitTrace a) :=
  rawMarkedFirstHitKernel a v H ∘ₖ stateFilter (lastRegeneration_measurable a)

lemma rawRegMarkedFirstHit_mass_le_one (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    rawRegMarkedFirstHitKernel a v H h univ ≤ 1 := by
  rw [rawRegMarkedFirstHitKernel,stateFilter_input]
  by_cases hReg : h ∈ lastRegeneration a
  · rw [ite_eq_left hReg]
    let z := decodeReturnedOdd (rawLast a h)
    have hz : rawLast a h=embedOdd z := (embed_decodeReturnedOdd_of_regeneration _ hReg).symm
    rw [rawMarkedFirstHit_mass a v H h z hz]
    exact ordinaryMarkedHit_mass_le_one v H z
  · simp [hReg]

instance rawRegMarkedFirstHitKernel_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (rawRegMarkedFirstHitKernel a v H) :=
  ⟨⟨1,by simp,rawRegMarkedFirstHit_mass_le_one a v H⟩⟩

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma kernel_power_sfinite (K : Kernel α α) [IsSFiniteKernel K] (n : ℕ) : IsSFiniteKernel (K^n) := by
  induction n with
  | zero => change IsSFiniteKernel (Kernel.id : Kernel α α); infer_instance
  | succ n ih => rw [pow_succ']; change IsSFiniteKernel (K ∘ₖ (K^n)); infer_instance

lemma kernel_power_support (K : Kernel α α) [IsSFiniteKernel K] {S : Set α} (hS : MeasurableSet S)
    (hK : ∀ x, ∀ᵐ y ∂K x, y ∈ S) (n : ℕ) (x : α) (hx : x ∈ S) :
    ∀ᵐ y ∂(K^n) x, y ∈ S := by
  have (m : ℕ) : IsSFiniteKernel (K^m) := kernel_power_sfinite K m
  cases n with
  | zero => change ∀ᵐ y ∂Measure.dirac x, y ∈ S; exact (ae_dirac_iff hS).mpr hx
  | succ n =>
    rw [pow_succ']
    change ∀ᵐ y ∂(K ∘ₖ (K^n)) x, y ∈ S
    exact Kernel.ae_comp_of_ae_ae hS (Eventually.of_forall hK)

lemma supported_projection_power (K : Kernel α α) (L : Kernel β β) [IsSFiniteKernel K] [IsSFiniteKernel L]
    {S : Set α} (_hS : MeasurableSet S) (hSupp : ∀ x, ∀ᵐ y ∂K x, y ∈ S)
    {f : α → β} (hf : Measurable f) (hKL : ∀ x ∈ S, (K x).map f=L (f x))
    (n : ℕ) (x : α) (hx : x ∈ S) : ((K^n) x).map f=(L^n) (f x) := by
  have (m : ℕ) : IsSFiniteKernel (K^m) := kernel_power_sfinite K m
  have (m : ℕ) : IsSFiniteKernel (L^m) := kernel_power_sfinite L m
  induction n generalizing x with
  | zero => change (Measure.dirac x).map f=Measure.dirac (f x); exact Measure.map_dirac' hf x
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    have hp : K^(n+1)=(K^n) ∘ₖ K := pow_succ _ _
    have hq : L^(n+1)=(L^n) ∘ₖ L := pow_succ _ _
    rw [lintegral_map hF hf,hp,hq,Kernel.lintegral_comp _ _ _ (g := fun z => F (f z)) (hF.comp hf),
      Kernel.lintegral_comp _ _ _ hF]
    have he : (fun y => ∫⁻ z, F (f z) ∂(K^n) y) =ᵐ[K x] fun y => ∫⁻ z, F z ∂(L^n) (f y) := by
      filter_upwards [hSupp x] with y hy
      rw [← lintegral_map (g := f) hF hf,ih y hy]
    rw [lintegral_congr_ae he]
    have hJ : Measurable (fun y : β => ∫⁻ z, F z ∂(L^n) y) := hF.lintegral_kernel
    rw [← lintegral_map (g := f) hJ hf,hKL x hx]

lemma supported_projection_potential (K B : Kernel α α) (L C : Kernel β β)
    [IsSFiniteKernel K] [IsSFiniteKernel B] [IsSFiniteKernel L] [IsSFiniteKernel C]
    {S : Set α} (hS : MeasurableSet S) (hSupp : ∀ x, ∀ᵐ y ∂K x, y ∈ S)
    {f : α → β} (hf : Measurable f) (hKL : ∀ x ∈ S, (K x).map f=L (f x))
    (hBC : ∀ x ∈ S, (B x).map f=C (f x)) (x : α) (hx : x ∈ S) :
    (potential B K x).map f=potential C L (f x) := by
  have (m : ℕ) : IsSFiniteKernel (K^m) := kernel_power_sfinite K m
  have (m : ℕ) : IsSFiniteKernel (L^m) := kernel_power_sfinite L m
  rw [potential,Kernel.sum_apply,Measure.map_sum (f := f) hf.aemeasurable,potential,Kernel.sum_apply]
  apply congrArg Measure.sum
  funext n
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf,Kernel.lintegral_comp _ _ _ (g := fun z => F (f z)) (hF.comp hf),
    Kernel.lintegral_comp _ _ _ hF]
  have he : (fun y => ∫⁻ z, F (f z) ∂B y) =ᵐ[(K^n) x] fun y => ∫⁻ z, F z ∂C (f y) := by
    filter_upwards [kernel_power_support K hS hSupp n x hx] with y hy
    rw [← lintegral_map (g := f) hF hf,hBC y hy]
  rw [lintegral_congr_ae he]
  have hJ : Measurable (fun y : β => ∫⁻ z, F z ∂C y) := hF.lintegral_kernel
  rw [← lintegral_map (g := f) hJ hf,supported_projection_power K L hS hSupp hf hKL n x hx]

noncomputable def kernelScale (p : ℝ≥0∞) (B : Kernel α β) [IsSFiniteKernel B] : Kernel α β :=
  B.withDensity (fun _ _ => p)

lemma kernelScale_apply (p : ℝ≥0∞) (B : Kernel α β) [IsSFiniteKernel B] (x : α) :
    kernelScale p B x=p • B x := by
  rw [kernelScale,Kernel.withDensity_apply _ (f := fun _ _ => p) measurable_const,withDensity_const]

lemma kernelScale_isSFinite (p : ℝ≥0∞) (hp : p ≠ ∞) (B : Kernel α β) [IsSFiniteKernel B] :
    IsSFiniteKernel (kernelScale p B) := Kernel.IsSFiniteKernel.withDensity B (fun _ _ => hp)

lemma potential_scale_base (p : ℝ≥0∞) (hp : p ≠ ∞) (B : Kernel α β) (K : Kernel α α)
    [IsSFiniteKernel B] [IsSFiniteKernel K] (x : α) :
    potential (kernelScale p B) K x=p • potential B K x := by
  have : IsSFiniteKernel (kernelScale p B) := kernelScale_isSFinite p hp B
  have (n : ℕ) : IsSFiniteKernel (K^n) := kernel_power_sfinite K n
  ext S hS
  rw [potential,Kernel.sum_apply' _ _ hS,Measure.smul_apply,smul_eq_mul,
    potential,Kernel.sum_apply' _ _ hS,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  rw [Kernel.comp_apply' _ _ _ hS,Kernel.comp_apply' _ _ _ hS]
  simp_rw [kernelScale_apply,Measure.smul_apply,smul_eq_mul]
  exact lintegral_const_mul' _ _ hp

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.KernelPotential

noncomputable def costWindowFilter (v H : ℝ) : Kernel ℝ ℝ :=
  stateFilter (S := Icc v (v+H)) measurableSet_Icc

noncomputable def costOutsideFilter (v H : ℝ) : Kernel ℝ ℝ :=
  stateFilter (S := (Icc v (v+H))ᶜ) measurableSet_Icc.compl

instance costWindowFilter_isFiniteKernel (v H : ℝ) : IsFiniteKernel (costWindowFilter v H) := by
  unfold costWindowFilter
  infer_instance
instance costOutsideFilter_isFiniteKernel (v H : ℝ) : IsFiniteKernel (costOutsideFilter v H) := by
  unfold costOutsideFilter
  infer_instance

noncomputable def costMarkedLoop (v H : ℝ) : Kernel ℝ ℝ := markedClockKernel ∘ₖ costOutsideFilter v H
instance costMarkedLoop_isFiniteKernel (v H : ℝ) : IsFiniteKernel (costMarkedLoop v H) := by
  unfold costMarkedLoop
  infer_instance

noncomputable def costCurrentHit (v H : ℝ) : Kernel ℝ ℝ :=
  potential (costWindowFilter v H) (costMarkedLoop v H)
instance costCurrentHit_isSFiniteKernel (v H : ℝ) : IsSFiniteKernel (costCurrentHit v H) := by
  unfold costCurrentHit
  infer_instance

instance costWindow_stopping_isMarkov (v H : ℝ) : IsMarkovKernel (costWindowFilter v H+costMarkedLoop v H) := by
  unfold costWindowFilter costMarkedLoop costOutsideFilter
  infer_instance

lemma costCurrentHit_mass_le_one (v H T : ℝ) : costCurrentHit v H T univ ≤ 1 :=
  capturePotential_mass_le_one _ _ T

noncomputable def ordinaryMarkedLoop (v H : ℝ) : Kernel OddCost OddCost :=
  rawBeginningKernel ∘ₖ stateFilter (ordinaryCostWindow_measurable v H).compl
instance ordinaryMarkedLoop_isSFiniteKernel (v H : ℝ) : IsSFiniteKernel (ordinaryMarkedLoop v H) := by
  unfold ordinaryMarkedLoop
  infer_instance

lemma rawBeginning_total_cost (z : OddCost) (hz : z ∈ returnSet) :
    (rawBeginningKernel z).map Prod.snd=markedClockKernel z.2 := by
  rw [markedClockKernel_apply]
  calc
    _ = ((rawBeginningKernel z).map (fun y => y.2-z.2)).map (fun G : ℝ => z.2+G) := by
      rw [Measure.map_map (g := fun G : ℝ => z.2+G) (f := fun y : OddCost => y.2-z.2)
        (measurable_const.add measurable_id) (measurable_snd.sub measurable_const)]
      congr 1
      funext y
      simp only [Function.comp_def,add_sub_cancel]
    _ = _ := by rw [rawBeginning_cost_law z hz]

lemma ordinaryMarkedLoop_support (v H : ℝ) (z : OddCost) :
    ∀ᵐ y ∂ordinaryMarkedLoop v H z, y ∈ returnSet := by
  rw [ordinaryMarkedLoop,stateFilter_input]
  split_ifs
  · exact rawBeginning_ae_regeneration z
  · simp

lemma ordinaryMarkedLoop_cost (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    (ordinaryMarkedLoop v H z).map Prod.snd=costMarkedLoop v H z.2 := by
  rw [ordinaryMarkedLoop,costMarkedLoop,costOutsideFilter,stateFilter_input,stateFilter_input]
  by_cases h : z.2 ∈ Icc v (v+H)
  · rw [ite_eq_right (show z ∉ (ordinaryCostWindow v H)ᶜ from fun hn => hn h),
      ite_eq_right (show z.2 ∉ (Icc v (v+H))ᶜ from fun hn => hn h),Measure.map_zero]
  · rw [ite_eq_left (show z ∈ (ordinaryCostWindow v H)ᶜ from h),
      ite_eq_left (show z.2 ∈ (Icc v (v+H))ᶜ from h)]
    exact rawBeginning_total_cost z hz

lemma cost_filter_projection (v H : ℝ) (z : OddCost) :
    (stateFilter (ordinaryCostWindow_measurable v H) z).map Prod.snd=costWindowFilter v H z.2 := by
  rw [stateFilter,costWindowFilter,stateFilter,Kernel.restrict_apply,Kernel.restrict_apply,Kernel.id_apply,Kernel.id_apply]
  change ((Measure.dirac z).restrict (Prod.snd ⁻¹' Icc v (v+H))).map Prod.snd =
    (Measure.dirac z.2).restrict (Icc v (v+H))
  rw [← Measure.restrict_map measurable_snd measurableSet_Icc,Measure.map_dirac' measurable_snd]

lemma ordinaryWindowCapture_on_regeneration (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    ordinaryWindowCapture v H z=markProbability • stateFilter (ordinaryCostWindow_measurable v H) z := by
  have hp : nextMarkWeight z=markProbability := cycleBranch_true_mass z hz
  rw [ordinaryWindowCapture,Kernel.restrict_apply,markInputWeightKernel_apply,hp,Measure.restrict_smul]
  rfl

lemma ordinaryWindowCapture_cost (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    (ordinaryWindowCapture v H z).map Prod.snd=kernelScale markProbability (costWindowFilter v H) z.2 := by
  rw [ordinaryWindowCapture_on_regeneration v H z hz,Measure.map_smul _ measurable_snd.aemeasurable,cost_filter_projection,kernelScale_apply]

theorem ordinaryMarkedPotential_cost (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    (potential (ordinaryWindowCapture v H) (ordinaryMarkedLoop v H) z).map Prod.snd =
      markProbability • costCurrentHit v H z.2 := by
  have : IsSFiniteKernel (kernelScale markProbability (costWindowFilter v H)) :=
    kernelScale_isSFinite markProbability markProbability_ne_top _
  rw [supported_projection_potential (ordinaryMarkedLoop v H) (ordinaryWindowCapture v H)
    (costMarkedLoop v H) (kernelScale markProbability (costWindowFilter v H))
    returnSet_measurable (ordinaryMarkedLoop_support v H) measurable_snd
    (ordinaryMarkedLoop_cost v H) (ordinaryWindowCapture_cost v H) z hz,
    potential_scale_base markProbability markProbability_ne_top]
  rfl

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.TransitionKernels
open NumberTheoryLean.KernelPotential

lemma unmarkedStar_support (z : OddCost) (hz : z ∈ returnSet) :
    ∀ᵐ y ∂unmarkedStar z, y ∈ returnSet := by
  rw [unmarkedStar,potential,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.id_comp]
  exact cycleBranch_pow_ae_regeneration false n z hz

lemma ordinaryMarkedPotential_mass (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    potential (ordinaryWindowCapture v H) (ordinaryMarkedLoop v H) z univ =
      markProbability*costCurrentHit v H z.2 univ := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) (ordinaryMarkedPotential_cost v H z hz)
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ,Measure.smul_apply,smul_eq_mul] at he
  exact he

theorem ordinaryMarkedHit_first_mark_reduction (v H : ℝ) (z : OddCost) (hz : z ∈ returnSet) :
    ordinaryMarkedHit v H z univ =
      ∫⁻ y, costCurrentHit v H y.2 univ ∂rawFirstMarkedBeginning z := by
  have hQ : Measurable (fun y : OddCost => costCurrentHit v H y.2 univ) :=
    ((costCurrentHit v H).measurable_coe MeasurableSet.univ).comp measurable_snd
  rw [ordinaryMarkedHit_denested,Kernel.comp_apply' _ _ _ MeasurableSet.univ,
    rawFirstMarkedBeginning,Kernel.withDensity_apply _ (f := fun _ y : OddCost => nextMarkWeight y)
      (nextMarkWeight_measurable.comp measurable_snd),
    lintegral_withDensity_eq_lintegral_mul _ nextMarkWeight_measurable hQ]
  change (∫⁻ y, potential (ordinaryWindowCapture v H) (ordinaryMarkedLoop v H) y univ ∂unmarkedStar z) =
    ∫⁻ y, nextMarkWeight y*costCurrentHit v H y.2 univ ∂unmarkedStar z
  apply lintegral_congr_ae
  filter_upwards [unmarkedStar_support z hz] with y hy
  rw [ordinaryMarkedPotential_mass v H y hy]
  have hp : nextMarkWeight y=markProbability := cycleBranch_true_mass y hy
  rw [hp]

noncomputable def ordinaryInitialHitMass (s : EvenState) (v H : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ordinaryMarkedHit v H z univ ∂delayedRegeneration s

lemma ordinaryInitialHitMass_le_one (s : EvenState) (v H : ℝ) : ordinaryInitialHitMass s v H ≤ 1 := by
  calc
    _ ≤ ∫⁻ _z, (1:ℝ≥0∞) ∂delayedRegeneration s := lintegral_mono (ordinaryMarkedHit_mass_le_one v H)
    _ = 1 := by simp

theorem ordinaryInitialHit_cost_law (s : EvenState) (v H : ℝ) :
    ordinaryInitialHitMass s v H = ∫⁻ T, costCurrentHit v H T univ ∂initialMarkedCostLaw s := by
  have hQ : Measurable (fun y : OddCost => costCurrentHit v H y.2 univ) :=
    ((costCurrentHit v H).measurable_coe MeasurableSet.univ).comp measurable_snd
  rw [ordinaryInitialHitMass,initialMarkedCostLaw,
    lintegral_map ((costCurrentHit v H).measurable_coe MeasurableSet.univ) measurable_snd,
    initialMarkedBeginning,Kernel.lintegral_comp _ _ _ hQ]
  apply lintegral_congr_ae
  filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
  exact ordinaryMarkedHit_first_mark_reduction v H z hz

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
