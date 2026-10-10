import OAI.NumberTheory.Jacobsthal.Paths.BranchWordEndpoint

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess

noncomputable def lookaheadInputCost : (w : List Bool) → (b : Bool) →
    CycleWordSignature (w++[b]).length → ℝ
  | [], _b, s => s.1.1
  | _c::w, b, s => lookaheadInputCost w b s.2

lemma lookaheadInputCost_measurable (w : List Bool) : ∀ b, Measurable (lookaheadInputCost w b) := by
  induction w with
  | nil => intro b; exact measurable_fst.comp measurable_fst
  | cons c w ih => intro b; exact (ih b).comp measurable_snd

lemma sourceBranchWitness_mass (b : Bool) (z : OddCost) :
    sourceBranchWitnessKernel b z univ=cycleBranchKernel b z univ := by
  have he := congrArg (fun μ : Measure OddCost => μ univ) (sourceBranchWitness_endpoint b z)
  rw [Measure.map_apply (f := fun w : SourceCycleWitness => w.2.2)
    (measurable_snd.comp measurable_snd) MeasurableSet.univ,preimage_univ] at he
  exact he

lemma sourceLookahead_lintegral (w : List Bool) (b : Bool) {F : ℝ → ℝ≥0∞} (hF : Measurable F) : ∀ z,
    (∫⁻ s, F (lookaheadInputCost w b s) ∂sourceMarkedWordKernel (w++[b]) z) =
      ∫⁻ y, cycleBranchKernel b y univ*F y.2 ∂branchWordKernel w z := by
  have hG : Measurable (fun y : OddCost => cycleBranchKernel b y univ*F y.2) :=
    ((cycleBranchKernel b).measurable_coe MeasurableSet.univ).mul (hF.comp measurable_snd)
  induction w with
  | nil =>
    intro z
    change (∫⁻ s : CycleWordSignature [b].length, F (lookaheadInputCost [] b s) ∂sourceMarkedWordKernel [b] z) = _
    rw [sourceMarkedWord_cons_lintegral b [] z
      (F := fun s => F (lookaheadInputCost [] b s)) (hF.comp (lookaheadInputCost_measurable [] b))]
    change (∫⁻ y : SourceCycleWitness, ∫⁻ _s, F z.2 ∂Measure.dirac (NumberTheoryLean.PairedCostGrouping.embedOdd y.2.2)
      ∂sourceBranchWitnessKernel b z) = ∫⁻ y, cycleBranchKernel b y univ*F y.2 ∂Measure.dirac z
    simp only [lintegral_const,measure_univ,mul_one]
    rw [sourceBranchWitness_mass,lintegral_dirac' z hG]
    exact mul_comm _ _
  | cons c w ih =>
    intro z
    change (∫⁻ s : CycleWordSignature (c::(w++[b])).length,
      F (lookaheadInputCost (c::w) b s) ∂sourceMarkedWordKernel (c::(w++[b])) z) = _
    rw [sourceMarkedWord_cons_lintegral c (w++[b]) z
        (F := fun s => F (lookaheadInputCost (c::w) b s))
        (hF.comp (lookaheadInputCost_measurable (c::w) b))]
    change (∫⁻ y : SourceCycleWitness, ∫⁻ s, F (lookaheadInputCost w b s)
      ∂sourceMarkedWordKernel (w++[b]) y.2.2 ∂sourceBranchWitnessKernel c z) = _
    simp_rw [ih]
    have hJ : Measurable (fun y : OddCost => ∫⁻ t, cycleBranchKernel b t univ*F t.2 ∂branchWordKernel w y) :=
      hG.lintegral_kernel
    rw [← lintegral_map (g := fun y : SourceCycleWitness => y.2.2) hJ (measurable_snd.comp measurable_snd),
      sourceBranchWitness_endpoint,branchWordKernel,Kernel.lintegral_comp _ _ _ hG]

theorem sourceLookahead_cost_law (w : List Bool) (b : Bool) (z : OddCost) :
    (sourceMarkedWordKernel (w++[b]) z).map (lookaheadInputCost w b) =
      ((branchWordKernel w z).withDensity (fun y => cycleBranchKernel b y univ)).map Prod.snd := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (lookaheadInputCost_measurable w b),lintegral_map hF measurable_snd,
    lintegral_withDensity_eq_lintegral_mul _ (g := fun y : OddCost => F y.2) ((cycleBranchKernel b).measurable_coe MeasurableSet.univ)
      (hF.comp measurable_snd)]
  exact sourceLookahead_lintegral w b hF z

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.PairedCostGrouping

noncomputable def rawLookaheadCostLaw (a : ℕ) (w : List Bool) (b : Bool) (h : RawHistory a) : Measure ℝ :=
  (rawMarkedWordKernel a (w++[b]) h).map (fun t =>
    lookaheadInputCost w b (rawCycleWordSignature a (w++[b]).length t)-(rawLast a h).2)

theorem rawLookaheadCostLaw_eq (a : ℕ) (w : List Bool) (b : Bool) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    rawLookaheadCostLaw a w b h =
      ((branchWordKernel w z).withDensity (fun y => cycleBranchKernel b y univ)).map (fun y => y.2-z.2) := by
  have hcost : (rawLast a h).2=z.2 := congrArg (fun s : NumberTheoryLean.FinitePathMeasures.CostState => s.2) hz
  rw [rawLookaheadCostLaw,hcost]
  calc
    _ = (((rawMarkedWordKernel a (w++[b]) h).map (rawCycleWordSignature a (w++[b]).length)).map
        (lookaheadInputCost w b)).map (fun T : ℝ => T-z.2) := by
      rw [Measure.map_map (g := fun T : ℝ => T-z.2) (measurable_id.sub measurable_const)
        (lookaheadInputCost_measurable w b),
        Measure.map_map (g := (fun T : ℝ => T-z.2) ∘ lookaheadInputCost w b)
          (f := rawCycleWordSignature a (w++[b]).length)
          ((measurable_id.sub measurable_const).comp (lookaheadInputCost_measurable w b))
          (rawCycleWordSignature_measurable _ _)]
      rfl
    _ = (((branchWordKernel w z).withDensity (fun y => cycleBranchKernel b y univ)).map Prod.snd).map
        (fun T : ℝ => T-z.2) := by
      rw [rawMarkedWord_signature (w++[b]) a h z hz,sourceLookahead_cost_law]
    _ = _ := by
      rw [Measure.map_map (g := fun T : ℝ => T-z.2) (measurable_id.sub measurable_const) measurable_snd]
      rfl

noncomputable def rawWaitingWordTerm (a n : ℕ) (h : RawHistory a) : Measure ℝ :=
  rawLookaheadCostLaw a (List.replicate n false) true h

noncomputable def rawSpacingWordTerm (a n : ℕ) (h : RawHistory a) : Measure ℝ :=
  markProbability⁻¹ • rawLookaheadCostLaw a (true::List.replicate n false) true h

theorem rawWaitingWordTerm_eq (a n : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) : rawWaitingWordTerm a n h=actualWaitingTerm n z := by
  rw [rawWaitingWordTerm,rawLookaheadCostLaw_eq a _ true h z hz,branchWordKernel_replicate,actualWaitingTerm]
  rfl

theorem rawSpacingWordTerm_eq (a n : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) : rawSpacingWordTerm a n h=actualSpacingTerm n z := by
  rw [rawSpacingWordTerm,rawLookaheadCostLaw_eq a _ true h z hz,
    branchWordKernel_first_replicate,actualSpacingTerm]
  rfl

noncomputable def rawWaitingCostLaw (a : ℕ) (h : RawHistory a) : Measure ℝ :=
  Measure.sum (fun n : ℕ => rawWaitingWordTerm a n h)

noncomputable def rawSpacingCostLaw (a : ℕ) (h : RawHistory a) : Measure ℝ :=
  Measure.sum (fun n : ℕ => rawSpacingWordTerm a n h)

theorem rawWaitingCostLaw_eq (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) : rawWaitingCostLaw a h=actualWaitingLaw z := by
  unfold rawWaitingCostLaw actualWaitingLaw
  apply congrArg Measure.sum
  funext n
  exact rawWaitingWordTerm_eq a n h z hz

theorem rawSpacingCostLaw_eq (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) : rawSpacingCostLaw a h=actualSpacingLaw z := by
  unfold rawSpacingCostLaw actualSpacingLaw
  apply congrArg Measure.sum
  funext n
  exact rawSpacingWordTerm_eq a n h z hz

theorem rawAllocatedCostLaws_mass_one (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) (hReg : z ∈ returnSet) :
    rawWaitingCostLaw a h univ=1 ∧ rawSpacingCostLaw a h univ=1 := by
  rw [rawWaitingCostLaw_eq a h z hz,rawSpacingCostLaw_eq a h z hz]
  exact ⟨actualWaitingLaw_mass z hReg,actualSpacingLaw_mass z hReg⟩

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.FirstHitKernels

lemma sourceCycleWitness_endpoint (z : OddCost) :
    (sourceCycleWitnessKernel z).map (fun w => w.2.2)=returnLaw z := by
  calc
    _ = ((sourceCycleWitnessKernel z).map Prod.snd).map Prod.snd :=
      (Measure.map_map measurable_snd measurable_snd).symm
    _ = _ := by
      rw [sourceCycleWitness_duration_law,NumberTheoryLean.MarkedCycleLaw.markedReturnLaw_forget]

noncomputable def rawReturnEndpointState (a : ℕ) (r : RawReturnTrace a) : CostState :=
  (rawReturnSignature a r).2.2

lemma rawReturnEndpointState_measurable (a : ℕ) : Measurable (rawReturnEndpointState a) :=
  (measurable_snd.comp measurable_snd).comp (rawReturnSignature_measurable a)

lemma rawReturnTrace_endpoint (a : ℕ) (h : RawHistory a) (z : OddCost) (hz : rawLast a h=embedOdd z) :
    (rawReturnTraceKernel a h).map (rawReturnEndpointState a)=(returnLaw z).map embedOdd := by
  have he := congrArg (fun μ : Measure ReturnSignature => μ.map (fun s => s.2.2))
    (rawReturnTrace_signature a h z hz)
  rw [Measure.map_map (g := fun s : ReturnSignature => s.2.2)
      (measurable_snd.comp measurable_snd) (rawReturnSignature_measurable a),
    Measure.map_map (g := fun s : ReturnSignature => s.2.2)
      (measurable_snd.comp measurable_snd) (sourceReturnSignature_measurable z)] at he
  rw [← sourceCycleWitness_endpoint z,
    Measure.map_map (g := embedOdd) (f := fun w : SourceCycleWitness => w.2.2)
      embedOdd_measurable (measurable_snd.comp measurable_snd)]
  exact he

noncomputable def rawReturnPastState (a : ℕ) (r : RawReturnTrace a) : CostState :=
  r.2 ⟨a,Finset.mem_Iic.mpr (by omega)⟩

lemma rawReturnPastState_measurable (a : ℕ) : Measurable (rawReturnPastState a) := by
  apply measurable_sigma_family
  intro n
  change Measurable (fun h : RawHistory (a+2*(n+1)) => h ⟨a,Finset.mem_Iic.mpr (by omega)⟩)
  exact measurable_pi_apply _

local instance : MeasurableSingletonClass State := by
  constructor
  intro x
  cases x with
  | inl e => simpa only [image_singleton] using ((measurableSet_singleton e).inl_image : MeasurableSet (Sum.inl '' {e} : Set State))
  | inr o => simpa only [image_singleton] using ((measurableSet_singleton o).inr_image : MeasurableSet (Sum.inr '' {o} : Set State))

lemma rawReturnPastState_ae (a : ℕ) (h : RawHistory a) :
    ∀ᵐ r ∂rawReturnTraceKernel a h, rawReturnPastState a r=rawLast a h := by
  have hm : MeasurableSet {r : RawReturnTrace a | rawReturnPastState a r=rawLast a h} :=
    (rawReturnPastState_measurable a) (measurableSet_singleton _)
  rw [rawReturnTraceKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.map_apply _ (rawReturnTrace_mk_measurable a n)]
  apply (ae_map_iff (rawReturnTrace_mk_measurable a n).aemeasurable hm).mpr
  filter_upwards [firstReturnHistory_retains_past a n h] with y hy
  exact congrFun hy (⟨a,by simp⟩ : Finset.Iic a)

lemma rawReturnTrace_input_endpoint (a : ℕ) (h : RawHistory a) (z : OddCost) (hz : rawLast a h=embedOdd z) :
    (rawReturnTraceKernel a h).map (fun r => (rawReturnPastState a r,rawReturnEndpointState a r)) =
      (returnLaw z).map (fun y => (embedOdd z,embedOdd y)) := by
  have he : (fun r => (rawReturnPastState a r,rawReturnEndpointState a r)) =ᵐ[rawReturnTraceKernel a h]
      fun r => (embedOdd z,rawReturnEndpointState a r) := by
    filter_upwards [rawReturnPastState_ae a h] with r hr
    exact Prod.ext (hr.trans hz) rfl
  calc
    _ = (rawReturnTraceKernel a h).map (fun r => (embedOdd z,rawReturnEndpointState a r)) := Measure.map_congr he
    _ = ((rawReturnTraceKernel a h).map (rawReturnEndpointState a)).map (fun y => (embedOdd z,y)) := by
      rw [Measure.map_map (g := fun y : CostState => (embedOdd z,y))
        (measurable_const.prodMk measurable_id) (rawReturnEndpointState_measurable a)]
      rfl
    _ = _ := by
      rw [rawReturnTrace_endpoint a h z hz,
        Measure.map_map (g := fun y : CostState => (embedOdd z,y))
          (measurable_const.prodMk measurable_id) embedOdd_measurable]
      rfl

abbrev RawContinuationTrace (a : ℕ) := RawHistory a ⊕ RawReturnTrace a

noncomputable def rawContinuationKernel (a : ℕ) : Kernel (RawHistory a) (RawContinuationTrace a) := by
  classical
  exact Kernel.piecewise (lastRegeneration_measurable a)
    ((Kernel.id : Kernel (RawHistory a) (RawHistory a)).map Sum.inl)
    ((rawReturnTraceKernel a).map Sum.inr)

instance rawContinuationKernel_isFiniteKernel (a : ℕ) : IsFiniteKernel (rawContinuationKernel a) := by
  classical
  unfold rawContinuationKernel
  infer_instance

noncomputable def rawContinuationSignature (a : ℕ) : RawContinuationTrace a → CostState × CostState :=
  Sum.elim (fun h => (rawLast a h,rawLast a h))
    (fun r => (rawReturnPastState a r,rawReturnEndpointState a r))

lemma rawContinuationSignature_measurable (a : ℕ) : Measurable (rawContinuationSignature a) :=
  ((rawLast_measurable a).prodMk (rawLast_measurable a)).sumElim
    ((rawReturnPastState_measurable a).prodMk (rawReturnEndpointState_measurable a))

theorem rawContinuation_signature (a : ℕ) (h : RawHistory a) (z : OddCost) (hz : rawLast a h=embedOdd z) :
    (rawContinuationKernel a h).map (rawContinuationSignature a) =
      (hitOrReturn z).map (fun y => (embedOdd z,embedOdd y)) := by
  classical
  have hp : h ∈ lastRegeneration a ↔ z ∈ returnSet := by
    change rawLast a h ∈ regenerationSet ↔ z ∈ returnSet
    rw [hz]
    rfl
  by_cases hReg : z ∈ returnSet
  · rw [rawContinuationKernel,Kernel.piecewise_apply,ite_eq_left (hp.mpr hReg),
      Kernel.map_apply _ measurable_inl,Kernel.id_apply,Measure.map_dirac' measurable_inl,
      Measure.map_dirac' (rawContinuationSignature_measurable a),
      hitOrReturn,Kernel.piecewise_apply,ite_eq_left hReg,Kernel.id_apply,
      Measure.map_dirac' (measurable_const.prodMk embedOdd_measurable)]
    congr 1
    exact Prod.ext hz hz
  · rw [rawContinuationKernel,Kernel.piecewise_apply,ite_eq_right (fun he => hReg (hp.mp he)),
      Kernel.map_apply _ measurable_inr,
      Measure.map_map (rawContinuationSignature_measurable a) measurable_inr,
      hitOrReturn,Kernel.piecewise_apply,ite_eq_right hReg]
    exact rawReturnTrace_input_endpoint a h z hz

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.TransitionKernels
open NumberTheoryLean.InitialOddDraw NumberTheoryLean.InitialRegeneration

lemma rawExtension_last_step (a : ℕ) (h : RawHistory a) :
    (rawExtension a (a+1) h).map (rawLast (a+1))=costKernel (rawLast a h) := by
  have he := congrArg (fun K : Kernel (RawHistory a) CostState => K h)
    (Kernel.map_partialTraj_succ_self (X := fun _ => CostState) (κ := historyKernel) a)
  change ((rawExtension a (a+1)).map (rawLast (a+1))) h=costKernel (rawLast a h) at he
  rw [Kernel.map_apply _ (rawLast_measurable (a+1))] at he
  exact he

lemma rawFirstOdd_draw_law (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) :
    (rawExtension a (a+1) h).map (rawLast (a+1))=(firstOdd s).map embedOdd := by
  rw [rawExtension_last_step,hs,firstOdd_full_draw]

noncomputable def oddCostStates : Set CostState := Prod.fst ⁻¹' Set.range (Sum.inr : OddState → State)

lemma oddCostStates_measurable : MeasurableSet oddCostStates :=
  measurableSet_range_inr.preimage measurable_fst

lemma embedOdd_mem_oddCostStates (z : OddCost) : embedOdd z ∈ oddCostStates := ⟨z.1,rfl⟩

lemma embed_decodeReturnedOdd_of_oddCostStates (s : CostState) (hs : s ∈ oddCostStates) :
    embedOdd (decodeReturnedOdd s)=s := by
  rcases s with ⟨s,T⟩
  rcases hs with ⟨o,ho⟩
  change Sum.inr o=s at ho
  subst s
  rfl

lemma rawFirstOdd_ae_odd (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) :
    ∀ᵐ y ∂rawExtension a (a+1) h, rawLast (a+1) y ∈ oddCostStates := by
  apply (ae_map_iff (rawLast_measurable (a+1)).aemeasurable oddCostStates_measurable).mp
  rw [rawFirstOdd_draw_law a h s hs]
  apply (ae_map_iff embedOdd_measurable.aemeasurable oddCostStates_measurable).mpr
  exact Filter.Eventually.of_forall embedOdd_mem_oddCostStates

abbrev RawInitialEvenTrace (a : ℕ) := RawContinuationTrace (a+1)

noncomputable def rawInitialEvenKernel (a : ℕ) : Kernel (RawHistory a) (RawInitialEvenTrace a) :=
  rawContinuationKernel (a+1) ∘ₖ rawExtension a (a+1)

instance rawInitialEvenKernel_isFiniteKernel (a : ℕ) : IsFiniteKernel (rawInitialEvenKernel a) := by
  unfold rawInitialEvenKernel
  infer_instance

noncomputable def initialOddReturnJoint : Kernel EvenState (OddCost × OddCost) :=
  firstOdd ⊗ₖ hitOrReturn.prodMkLeft EvenState

instance initialOddReturnJoint_isMarkovKernel : IsMarkovKernel initialOddReturnJoint := by
  unfold initialOddReturnJoint
  infer_instance

noncomputable def embedOddPair (p : OddCost × OddCost) : CostState × CostState := (embedOdd p.1,embedOdd p.2)

lemma embedOddPair_measurable : Measurable embedOddPair :=
  (embedOdd_measurable.comp measurable_fst).prodMk (embedOdd_measurable.comp measurable_snd)

theorem rawInitialEven_joint_signature (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) :
    (rawInitialEvenKernel a h).map (rawContinuationSignature (a+1)) =
      (initialOddReturnJoint s).map embedOddPair := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (rawContinuationSignature_measurable _),rawInitialEvenKernel,
    Kernel.lintegral_comp _ _ _ (g := fun r => F (rawContinuationSignature (a+1) r))
      (hF.comp (rawContinuationSignature_measurable _)),
    lintegral_map hF embedOddPair_measurable,initialOddReturnJoint,
    Kernel.lintegral_compProd _ _ _ (f := fun p : OddCost × OddCost => F (embedOddPair p))
      (hF.comp embedOddPair_measurable)]
  let G : CostState → ℝ≥0∞ := fun c => ∫⁻ y, F (c,embedOdd y) ∂hitOrReturn (decodeReturnedOdd c)
  have hG : Measurable G := by
    let K : Kernel CostState OddCost := hitOrReturn.comap decodeReturnedOdd decodeReturnedOdd_measurable
    change Measurable (fun c : CostState => ∫⁻ y, F (c,embedOdd y) ∂K c)
    exact Measurable.lintegral_kernel_prod_right' (κ := K)
      (f := fun p : CostState × OddCost => F (p.1,embedOdd p.2))
      (hF.comp (measurable_fst.prodMk (embedOdd_measurable.comp measurable_snd)))
  have he : (fun y : RawHistory (a+1) => ∫⁻ r, F (rawContinuationSignature (a+1) r) ∂rawContinuationKernel (a+1) y)
      =ᵐ[rawExtension a (a+1) h] fun y => G (rawLast (a+1) y) := by
    filter_upwards [rawFirstOdd_ae_odd a h s hs] with y hy
    let z : OddCost := decodeReturnedOdd (rawLast (a+1) y)
    have hz : rawLast (a+1) y=embedOdd z := (embed_decodeReturnedOdd_of_oddCostStates _ hy).symm
    rw [← lintegral_map (g := rawContinuationSignature (a+1)) hF (rawContinuationSignature_measurable _),
      rawContinuation_signature (a+1) y z hz,
      lintegral_map (g := fun u : OddCost => (embedOdd z,embedOdd u)) hF
        (measurable_const.prodMk embedOdd_measurable)]
    change (∫⁻ u, F (embedOdd z,embedOdd u) ∂hitOrReturn z) =
      ∫⁻ u, F (rawLast (a+1) y,embedOdd u) ∂hitOrReturn z
    apply lintegral_congr
    intro u
    rw [hz]
  rw [lintegral_congr_ae he,← lintegral_map (g := rawLast (a+1)) hG (rawLast_measurable _),
    rawFirstOdd_draw_law a h s hs,lintegral_map hG embedOdd_measurable]
  rfl

def rawInitialEvenDuration (a : ℕ) : RawInitialEvenTrace a → ℕ :=
  Sum.elim (fun _ => 1) (fun r => 1+2*(r.1+1))

lemma rawInitialEvenDuration_positive (a : ℕ) (r : RawInitialEvenTrace a) : 0 < rawInitialEvenDuration a r := by
  cases r with
  | inl h => exact Nat.zero_lt_one
  | inr r => change 0 < 1+2*(r.1+1); omega

theorem rawInitialEven_mass_one (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) : rawInitialEvenKernel a h univ=1 := by
  have he := congrArg (fun μ : Measure (CostState × CostState) => μ univ) (rawInitialEven_joint_signature a h s hs)
  rw [Measure.map_apply (rawContinuationSignature_measurable _) MeasurableSet.univ,
    Measure.map_apply embedOddPair_measurable MeasurableSet.univ,preimage_univ,preimage_univ] at he
  exact he.trans measure_univ

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
