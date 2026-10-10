import OAI.NumberTheory.Jacobsthal.Paths.SourceWitnessSeries

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FinitePathGeometry

abbrev RawReturnTrace (a : ℕ) := Σ n : ℕ, RawHistory (a+2*(n+1))
abbrev ReturnSignature := ℕ × (CostState × CostState)

def packRawReturnTrace (a n : ℕ) (h : RawHistory (a+2*(n+1))) : RawReturnTrace a :=
  @Sigma.mk ℕ (fun k => RawHistory (a+2*(k+1))) n h

lemma rawReturnTrace_mk_measurable (a n : ℕ) :
    Measurable (packRawReturnTrace a n : RawHistory (a+2*(n+1)) → RawReturnTrace a) := by
  apply Measurable.of_le_map
  exact iInf_le _ n

noncomputable def rawReturnTraceKernel (a : ℕ) : Kernel (RawHistory a) (RawReturnTrace a) :=
  Kernel.sum (fun n : ℕ => (firstReturnHistory a n).map (packRawReturnTrace a n))

instance rawReturnTraceKernel_isSFiniteKernel (a : ℕ) : IsSFiniteKernel (rawReturnTraceKernel a) := by
  unfold rawReturnTraceKernel
  infer_instance

noncomputable def rawReturnSignature (a : ℕ) (r : RawReturnTrace a) : ReturnSignature :=
  (2*(r.1+1),rawCyclePairEval a (a+2*(r.1+1)) (by omega) r.2)

lemma rawReturnSignature_measurable (a : ℕ) : Measurable (rawReturnSignature a) := by
  intro S hS
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((fun h : RawHistory (a+2*(n+1)) =>
    (2*(n+1),rawCyclePairEval a (a+2*(n+1)) (by omega) h)) ⁻¹' S)
  exact (measurable_const.prodMk (rawCyclePairEval_measurable _ _ (by omega))) hS

noncomputable def sourceReturnSignature (z : OddCost) (w : SourceCycleWitness) : ReturnSignature :=
  (w.2.1,((Sum.inl w.1,z.2+cost w.1.1),embedOdd w.2.2))

lemma sourceReturnSignature_measurable (z : OddCost) : Measurable (sourceReturnSignature z) :=
  (measurable_fst.comp measurable_snd).prodMk
    (((measurable_inl.comp measurable_fst).prodMk
      (measurable_const.add (cost_measurable.comp (measurable_subtype_coe.comp measurable_fst)))).prodMk
      (embedOdd_measurable.comp (measurable_snd.comp measurable_snd)))

lemma sourceReturnSignature_injective (z : OddCost) : Function.Injective (sourceReturnSignature z) := by
  intro x y h
  have hn : x.2.1=y.2.1 := congrArg (fun r : ReturnSignature => r.1) h
  have he : x.1=y.1 := Sum.inl.inj (congrArg (fun r : ReturnSignature => r.2.1.1) h)
  have ho : embedOdd x.2.2=embedOdd y.2.2 := congrArg (fun r : ReturnSignature => r.2.2) h
  have hs : (embedOdd x.2.2).1=(embedOdd y.2.2).1 := congrArg (fun r : CostState => r.1) ho
  have hc : (embedOdd x.2.2).2=(embedOdd y.2.2).2 := congrArg (fun r : CostState => r.2) ho
  have hr : x.2.2=y.2.2 := Prod.ext (Sum.inr.inj hs) hc
  exact Prod.ext he (Prod.ext hn hr)

lemma rawReturnTerm_signature (a n : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (((firstReturnHistory a n).map (packRawReturnTrace a n)) h).map (rawReturnSignature a) =
      (sourceWitnessTerm n z).map (sourceReturnSignature z) := by
  rw [Kernel.map_apply _ (rawReturnTrace_mk_measurable a n),
    Measure.map_map (rawReturnSignature_measurable a) (rawReturnTrace_mk_measurable a n),
    sourceWitnessTerm,Kernel.map_apply _ (tagSourceReturn_measurable n),
    Measure.map_map (sourceReturnSignature_measurable z) (tagSourceReturn_measurable n)]
  have he := congrArg (fun μ : Measure (CostState × CostState) => μ.map (fun p => (2*(n+1),p)))
    (firstReturnHistory_joint a n h z hz)
  rw [Measure.map_map (g := fun p : CostState × CostState => (2*(n+1),p))
      (f := rawCyclePairEval a (a+2*(n+1)) (by omega))
      (measurable_const.prodMk measurable_id) (rawCyclePairEval_measurable _ _ (by omega)),
    Measure.map_map (g := fun p : CostState × CostState => (2*(n+1),p))
      (f := pairTraceOfWitness z) (measurable_const.prodMk measurable_id) (pairTraceOfWitness_measurable z)] at he
  exact he

theorem rawReturnTrace_signature (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (rawReturnTraceKernel a h).map (rawReturnSignature a) =
      (sourceCycleWitnessKernel z).map (sourceReturnSignature z) := by
  rw [rawReturnTraceKernel,Kernel.sum_apply,
    Measure.map_sum (rawReturnSignature_measurable a).aemeasurable,
    sourceCycleWitness_series,Kernel.sum_apply,
    Measure.map_sum (sourceReturnSignature_measurable z).aemeasurable]
  apply congrArg Measure.sum
  funext n
  exact rawReturnTerm_signature a n h z hz

theorem rawReturnTrace_mass_one (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) : rawReturnTraceKernel a h univ=1 := by
  have he := congrArg (fun μ : Measure ReturnSignature => μ univ) (rawReturnTrace_signature a h z hz)
  rw [Measure.map_apply (rawReturnSignature_measurable a) MeasurableSet.univ,
    Measure.map_apply (sourceReturnSignature_measurable z) MeasurableSet.univ,preimage_univ,
    preimage_univ] at he
  exact he.trans measure_univ

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels

noncomputable def twoReturnHistory (a n m : ℕ) :
    Kernel (RawHistory a) (RawHistory ((a+2*(n+1))+2*(m+1))) :=
  firstReturnHistory (a+2*(n+1)) m ∘ₖ firstReturnHistory a n

instance twoReturnHistory_isFiniteKernel (a n m : ℕ) : IsFiniteKernel (twoReturnHistory a n m) := by
  unfold twoReturnHistory
  infer_instance

noncomputable def twoReturnEvent (a n m : ℕ) : Set (RawHistory ((a+2*(n+1))+2*(m+1))) :=
  (rawPrefix (show a+2*(n+1) ≤ (a+2*(n+1))+2*(m+1) by omega) ⁻¹'
    (avoidOddReturns a n (a+2*(n+1)) (by omega) ∩ lastRegeneration (a+2*(n+1)))) ∩
    (avoidOddReturns (a+2*(n+1)) m ((a+2*(n+1))+2*(m+1)) (by omega) ∩
      lastRegeneration ((a+2*(n+1))+2*(m+1)))

lemma twoReturnEvent_measurable (a n m : ℕ) : MeasurableSet (twoReturnEvent a n m) :=
  (((avoidOddReturns_measurable a n (a+2*(n+1)) (by omega)).inter (lastRegeneration_measurable _)).preimage
    (rawPrefix_measurable (by omega))).inter
      ((avoidOddReturns_measurable (a+2*(n+1)) m ((a+2*(n+1))+2*(m+1)) (by omega)).inter
        (lastRegeneration_measurable _))

theorem twoReturnHistory_eq_cylinder (a n m : ℕ) :
    twoReturnHistory a n m =
      (rawExtension a ((a+2*(n+1))+2*(m+1))).restrict (twoReturnEvent_measurable a n m) := by
  rw [twoReturnHistory,firstReturnHistory,firstReturnHistory,
    ← rawExtension_restrict_comp (show a ≤ a+2*(n+1) by omega)
      (show a+2*(n+1) ≤ (a+2*(n+1))+2*(m+1) by omega)
      ((avoidOddReturns_measurable a n (a+2*(n+1)) (by omega)).inter (lastRegeneration_measurable _))
      ((avoidOddReturns_measurable (a+2*(n+1)) m ((a+2*(n+1))+2*(m+1)) (by omega)).inter
        (lastRegeneration_measurable _))]
  rfl

lemma twoReturnHistory_retains_past (a n m : ℕ) (h : RawHistory a) :
    ∀ᵐ r ∂twoReturnHistory a n m h,
      rawPrefix (show a ≤ (a+2*(n+1))+2*(m+1) by omega) r=h := by
  rw [twoReturnHistory_eq_cylinder,Kernel.restrict_apply]
  exact ae_restrict_of_ae (rawExtension_retains_prefix (by omega) h)

noncomputable def twoReturnHistoryWithFirsts (a n m : ℕ) {E F : Set CostState}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Kernel (RawHistory a) (RawHistory ((a+2*(n+1))+2*(m+1))) :=
  (twoReturnHistory a n m).restrict
    ((hE.preimage (measurable_pi_apply (⟨a+1,Finset.mem_Iic.mpr (by omega)⟩ :
      Finset.Iic ((a+2*(n+1))+2*(m+1))))).inter
      (hF.preimage (measurable_pi_apply (⟨(a+2*(n+1))+1,Finset.mem_Iic.mpr (by omega)⟩ :
        Finset.Iic ((a+2*(n+1))+2*(m+1))))))

lemma twoReturnHistoryWithFirsts_apply (a n m : ℕ) {E F : Set CostState}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (h : RawHistory a)
    {S : Set (RawHistory ((a+2*(n+1))+2*(m+1)))} (hS : MeasurableSet S) :
    twoReturnHistoryWithFirsts a n m hE hF h S = rawExtension a ((a+2*(n+1))+2*(m+1)) h
      ((S ∩ ({r | r ⟨a+1,Finset.mem_Iic.mpr (by omega)⟩ ∈ E} ∩
        {r | r ⟨(a+2*(n+1))+1,Finset.mem_Iic.mpr (by omega)⟩ ∈ F})) ∩ twoReturnEvent a n m) := by
  rw [twoReturnHistoryWithFirsts,Kernel.restrict_apply' _ _ _ hS,twoReturnHistory_eq_cylinder,
    Kernel.restrict_apply' _ _ _ (hS.inter ((hE.preimage (measurable_pi_apply _)).inter
      (hF.preimage (measurable_pi_apply _))))]
  rfl

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels

abbrev RawTwoReturnTrace (a : ℕ) :=
  Σ n : ℕ, Σ m : ℕ, RawHistory ((a+2*(n+1))+2*(m+1))

def packRawTwoReturnTrace (a n m : ℕ) (h : RawHistory ((a+2*(n+1))+2*(m+1))) : RawTwoReturnTrace a :=
  @Sigma.mk ℕ (fun i => Σ j : ℕ, RawHistory ((a+2*(i+1))+2*(j+1))) n
    (@Sigma.mk ℕ (fun j => RawHistory ((a+2*(n+1))+2*(j+1))) m h)

lemma measurableSigmaMk {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (i : ι) :
    Measurable (@Sigma.mk ι X i) := Measurable.of_le_map (iInf_le _ i)

lemma packRawTwoReturnTrace_measurable (a n m : ℕ) : Measurable (packRawTwoReturnTrace a n m) := by
  exact (measurableSigmaMk (X := fun i : ℕ => Σ j : ℕ, RawHistory ((a+2*(i+1))+2*(j+1))) n).comp
    (measurableSigmaMk (X := fun j : ℕ => RawHistory ((a+2*(n+1))+2*(j+1))) m)

noncomputable def rawTwoReturnTraceKernel (a : ℕ) : Kernel (RawHistory a) (RawTwoReturnTrace a) :=
  Kernel.sum (fun n : ℕ => Kernel.sum (fun m : ℕ =>
    (twoReturnHistory a n m).map (packRawTwoReturnTrace a n m)))

instance rawTwoReturnTraceKernel_isSFiniteKernel (a : ℕ) : IsSFiniteKernel (rawTwoReturnTraceKernel a) := by
  unfold rawTwoReturnTraceKernel
  infer_instance

lemma rawReturnTrace_mass_series (a : ℕ) (h : RawHistory a) :
    rawReturnTraceKernel a h univ = ∑' n : ℕ, firstReturnHistory a n h univ := by
  rw [rawReturnTraceKernel,Kernel.sum_apply' _ _ MeasurableSet.univ]
  apply tsum_congr
  intro n
  rw [Kernel.map_apply' _ (rawReturnTrace_mk_measurable a n) _ MeasurableSet.univ,preimage_univ]

lemma rawReturnTrace_mass_at_regeneration (a : ℕ) (h : RawHistory a)
    (hReg : rawLast a h ∈ regenerationSet) : rawReturnTraceKernel a h univ=1 := by
  rcases he : rawLast a h with ⟨s,T⟩
  cases s with
  | inl s =>
    rw [he] at hReg
    exact False.elim (regeneration_even s T hReg)
  | inr s => exact rawReturnTrace_mass_one a h (s,T) he

lemma rawTwoReturnTrace_mass_series (a : ℕ) (h : RawHistory a) :
    rawTwoReturnTraceKernel a h univ = ∑' n : ℕ, ∑' m : ℕ, twoReturnHistory a n m h univ := by
  rw [rawTwoReturnTraceKernel,Kernel.sum_apply' _ _ MeasurableSet.univ]
  apply tsum_congr
  intro n
  rw [Kernel.sum_apply' _ _ MeasurableSet.univ]
  apply tsum_congr
  intro m
  rw [Kernel.map_apply' _ (packRawTwoReturnTrace_measurable a n m) _ MeasurableSet.univ,preimage_univ]

theorem rawTwoReturnTrace_mass_conditioning (a : ℕ) (h : RawHistory a) :
    rawTwoReturnTraceKernel a h univ = ∑' n : ℕ,
      ∫⁻ y, rawReturnTraceKernel (a+2*(n+1)) y univ ∂firstReturnHistory a n h := by
  rw [rawTwoReturnTrace_mass_series]
  apply tsum_congr
  intro n
  simp_rw [twoReturnHistory,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  rw [← lintegral_tsum (f := fun (m : ℕ) (y : RawHistory (a+2*(n+1))) =>
    firstReturnHistory (a+2*(n+1)) m y univ)
    (fun m => ((firstReturnHistory (a+2*(n+1)) m).measurable_coe MeasurableSet.univ).aemeasurable)]
  apply lintegral_congr
  intro y
  exact (rawReturnTrace_mass_series _ y).symm

theorem rawTwoReturnTrace_mass_one (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) : rawTwoReturnTraceKernel a h univ=1 := by
  rw [rawTwoReturnTrace_mass_conditioning]
  have he (n : ℕ) : (∫⁻ y, rawReturnTraceKernel (a+2*(n+1)) y univ ∂firstReturnHistory a n h) =
      firstReturnHistory a n h univ := by
    have hae : (fun y => rawReturnTraceKernel (a+2*(n+1)) y univ) =ᵐ[firstReturnHistory a n h] fun _ => 1 := by
      filter_upwards [firstReturnHistory_ae_cylinder a n h] with y hy
      exact rawReturnTrace_mass_at_regeneration _ y hy.2
    rw [lintegral_congr_ae hae]
    simp
  simp_rw [he]
  rw [← rawReturnTrace_mass_series a h,rawReturnTrace_mass_one a h z hz]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels

lemma fullPairCaptured_add_killed : fullPairCaptured+fullPairKilled=costKernel^2 := by
  ext z : 1
  rw [_root_.add_apply,fullPairCaptured,fullPairKilled,Kernel.restrict_apply,Kernel.restrict_apply]
  exact Measure.restrict_add_restrict_compl regenerationSet_measurable

lemma fullPairReturn_mass_step (n : ℕ) (z : CostState) :
    fullPairReturn n z univ+(fullPairKilled^(n+1)) z univ=(fullPairKilled^n) z univ := by
  have : IsMarkovKernel (costKernel^2) := by rw [pow_two]; change IsMarkovKernel (costKernel ∘ₖ costKernel); infer_instance
  have hp : fullPairKilled^(n+1)=fullPairKilled ∘ₖ (fullPairKilled^n) := pow_succ' _ _
  calc
    _ = ((fullPairCaptured+fullPairKilled) ∘ₖ (fullPairKilled^n)) z univ := by
      rw [Kernel.comp_add_left,_root_.add_apply,Measure.add_apply,hp]
      rfl
    _ = ((costKernel^2) ∘ₖ (fullPairKilled^n)) z univ := by rw [fullPairCaptured_add_killed]
    _ = _ := by rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]; simp

lemma fullPairReturn_finite_mass (n : ℕ) (z : CostState) :
    (fullPairKilled^n) z univ+∑ k ∈ Finset.range n, fullPairReturn k z univ=1 := by
  induction n with
  | zero => change (Measure.dirac z) univ+0=1; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (∑ k ∈ Finset.range n, fullPairReturn k z univ)+
          (fullPairReturn n z univ+(fullPairKilled^(n+1)) z univ) := by ac_rfl
      _ = _ := by rw [fullPairReturn_mass_step]; simpa only [add_comm] using ih

lemma fullPairReturn_total_mass_le (z : CostState) :
    (∑' n : ℕ, fullPairReturn n z univ) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro n
  calc
    _ ≤ (fullPairKilled^n) z univ+∑ k ∈ Finset.range n, fullPairReturn k z univ := le_add_left le_rfl
    _ = 1 := fullPairReturn_finite_mass n z

lemma firstReturnHistory_mass_full (a n : ℕ) (h : RawHistory a) :
    firstReturnHistory a n h univ=fullPairReturn n (rawLast a h) univ := by
  have he := congrArg (fun K : Kernel (RawHistory a) CostState => K h univ)
    (firstReturnHistory_kernel_projection a n)
  rw [Kernel.map_apply' _ (rawLast_measurable _) _ MeasurableSet.univ,preimage_univ,Kernel.comap_apply] at he
  exact he

theorem rawReturnTrace_mass_le_one (a : ℕ) (h : RawHistory a) : rawReturnTraceKernel a h univ ≤ 1 := by
  rw [rawReturnTrace_mass_series]
  simp_rw [firstReturnHistory_mass_full]
  exact fullPairReturn_total_mass_le _

instance rawReturnTraceKernel_isFiniteKernel (a : ℕ) : IsFiniteKernel (rawReturnTraceKernel a) :=
  ⟨⟨1,by simp,rawReturnTrace_mass_le_one a⟩⟩

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
