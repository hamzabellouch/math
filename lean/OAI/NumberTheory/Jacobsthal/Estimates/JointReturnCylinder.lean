import OAI.NumberTheory.Jacobsthal.Paths.PairCaptureProjection

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.CostReturnLaw

lemma kernel_comp_comap {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (C : Kernel β γ) (K : Kernel α β)
    {f : δ → α} (hf : Measurable f) :
    C ∘ₖ (K.comap f hf) = (C ∘ₖ K).comap f hf := by
  ext x S hS
  rw [Kernel.comp_apply' _ _ _ hS,Kernel.comap_apply,Kernel.comap_apply,
    Kernel.comp_apply' _ _ _ hS]

lemma kernelProjection_power {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) (K : Kernel α α) (L : Kernel β β)
    (hKL : K.map f=L.comap f hf) (n : ℕ) :
    (K^n).map f=(L^n).comap f hf := by
  induction n with
  | zero =>
    change Kernel.id.map f = Kernel.id.comap f hf
    rw [Kernel.id_map hf,Kernel.id_comap hf]
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change (K ∘ₖ (K^n)).map f=(L ∘ₖ (L^n)).comap f hf
    rw [Kernel.map_comp,hKL,← Kernel.comp_map _ _ hf,ih,kernel_comp_comap]

lemma survivingHistory_zero (a : ℕ) : survivingHistory a 0 = Kernel.id := by
  ext h : 1
  rw [survivingHistory,Kernel.restrict_apply]
  have hs : avoidOddReturns a 0 (a+2*0) le_rfl = univ := by ext z; simp [avoidOddReturns]
  rw [hs,Measure.restrict_univ]
  change rawExtension a a h = Kernel.id h
  rw [rawExtension,Kernel.partialTraj_self]

lemma rawKilledPair_kernel_projection (a n : ℕ) :
    ((rawExtension (a+2*n) (a+2*(n+1))).restrict (lastRegeneration_measurable _).compl).map
      (rawLast (a+2*(n+1))) = fullPairKilled.comap (rawLast (a+2*n)) (rawLast_measurable _) := by
  rw [show a+2*(n+1)=(a+2*n)+2 by omega]
  ext h : 1
  rw [Kernel.map_apply _ (rawLast_measurable _),Kernel.comap_apply]
  exact rawKilledPair_projection (a+2*n) h

lemma rawCapturedPair_kernel_projection (a n : ℕ) :
    ((rawExtension (a+2*n) (a+2*(n+1))).restrict (lastRegeneration_measurable _)).map
      (rawLast (a+2*(n+1))) = fullPairCaptured.comap (rawLast (a+2*n)) (rawLast_measurable _) := by
  rw [show a+2*(n+1)=(a+2*n)+2 by omega]
  ext h : 1
  rw [Kernel.map_apply _ (rawLast_measurable _),Kernel.comap_apply]
  exact rawCapturedPair_projection (a+2*n) h

lemma survivingHistory_kernel_projection (a n : ℕ) :
    (survivingHistory a n).map (rawLast (a+2*n)) =
      (fullPairKilled^n).comap (rawLast a) (rawLast_measurable a) := by
  induction n with
  | zero =>
    rw [survivingHistory_zero]
    change Kernel.id.map (rawLast a) = Kernel.id.comap (rawLast a) (rawLast_measurable a)
    rw [Kernel.id_map (rawLast_measurable a),Kernel.id_comap (rawLast_measurable a)]
  | succ n ih =>
    rw [survivingHistory_succ,Kernel.map_comp,rawKilledPair_kernel_projection,
      ← Kernel.comp_map _ _ (rawLast_measurable _),ih,kernel_comp_comap]
    rw [pow_succ']
    rfl

noncomputable def fullPairReturn (n : ℕ) : Kernel CostState CostState :=
  fullPairCaptured ∘ₖ (fullPairKilled ^ n)

lemma firstReturnHistory_kernel_projection (a n : ℕ) :
    (firstReturnHistory a n).map (rawLast (a+2*(n+1))) =
      (fullPairReturn n).comap (rawLast a) (rawLast_measurable a) := by
  rw [firstReturnHistory_eq_capture_after_survival,Kernel.map_comp,rawCapturedPair_kernel_projection,
    ← Kernel.comp_map _ _ (rawLast_measurable _),survivingHistory_kernel_projection,kernel_comp_comap]
  rfl

lemma costKilled_kernel_projection :
    costKilled.map embedOdd = fullPairKilled.comap embedOdd embedOdd_measurable := by
  ext z : 1
  rw [Kernel.map_apply _ embedOdd_measurable,Kernel.comap_apply,costKilled_fullPair_projection]

lemma costCaptured_kernel_projection :
    costCaptured.map embedOdd = fullPairCaptured.comap embedOdd embedOdd_measurable := by
  ext z : 1
  rw [Kernel.map_apply _ embedOdd_measurable,Kernel.comap_apply,costCaptured_fullPair_projection]

lemma firstReturn_fullPair_projection (n : ℕ) (z : OddCost) :
    (firstReturn n z).map embedOdd = fullPairReturn n (embedOdd z) := by
  have he : (firstReturn n).map embedOdd = (fullPairReturn n).comap embedOdd embedOdd_measurable := by
    rw [firstReturn,Kernel.map_comp,costCaptured_kernel_projection,
      ← Kernel.comp_map _ _ embedOdd_measurable,
      kernelProjection_power embedOdd_measurable _ _ costKilled_kernel_projection n,kernel_comp_comap]
    rfl
  rw [← Kernel.map_apply _ embedOdd_measurable,he,Kernel.comap_apply]

theorem firstReturnHistory_endpoint (a n : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (firstReturnHistory a n h).map (rawLast (a+2*(n+1))) = (firstReturn n z).map embedOdd := by
  rw [← Kernel.map_apply _ (rawLast_measurable _),firstReturnHistory_kernel_projection,
    Kernel.comap_apply,hz,firstReturn_fullPair_projection]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels

noncomputable def returnCylinderTo (a n b : ℕ) (hab : a+2*(n+1) ≤ b) :
    Kernel (RawHistory a) (RawHistory b) :=
  (rawExtension a b).restrict
    ((avoidOddReturns_measurable a n b (by omega)).inter (lastRegeneration_measurable b))

lemma returnCylinderTo_exact (a n : ℕ) :
    returnCylinderTo a n (a+2*(n+1)) le_rfl = firstReturnHistory a n := rfl

lemma avoidOddReturns_first_pair (a n b : ℕ) (hab : a+2*(n+1) ≤ b) :
    avoidOddReturns a (n+1) b hab =
      (rawPrefix (show a+2 ≤ b by omega) ⁻¹' (lastRegeneration (a+2))ᶜ) ∩
        avoidOddReturns (a+2) n b (by omega) := by
  ext h
  change (∀ j : Fin (n+1), h ⟨a+2*(j.1+1),_⟩ ∉ regenerationSet) ↔
    h ⟨a+2,_⟩ ∉ regenerationSet ∧
      ∀ j : Fin n, h ⟨(a+2)+2*(j.1+1),_⟩ ∉ regenerationSet
  constructor
  · intro hh
    constructor
    · exact hh 0
    · intro j
      have hj := hh j.succ
      have he : (⟨a+2*(j.succ.1+1),Finset.mem_Iic.mpr (by have hj := j.2; simp; omega)⟩ : Finset.Iic b) =
          ⟨(a+2)+2*(j.1+1),Finset.mem_Iic.mpr (by have hj := j.2; omega)⟩ := by
        apply Subtype.ext
        simp only [Fin.val_succ]
        omega
      rw [he] at hj
      exact hj
  · rintro ⟨hfirst,htail⟩ j
    refine Fin.cases hfirst (fun k => ?_) j
    have he : (⟨a+2*(k.succ.1+1),Finset.mem_Iic.mpr (by have hk := k.2; simp; omega)⟩ : Finset.Iic b) =
        ⟨(a+2)+2*(k.1+1),Finset.mem_Iic.mpr (by have hk := k.2; omega)⟩ := by
      apply Subtype.ext
      simp only [Fin.val_succ]
      omega
    rw [he]
    exact htail k

theorem returnCylinderTo_first_pair (a n b : ℕ) (hab : a+2*(n+2) ≤ b) :
    returnCylinderTo a (n+1) b (by omega) =
      returnCylinderTo (a+2) n b (by omega) ∘ₖ
        ((rawExtension a (a+2)).restrict (lastRegeneration_measurable (a+2)).compl) := by
  unfold returnCylinderTo
  rw [← rawExtension_restrict_comp (show a ≤ a+2 by omega) (show a+2 ≤ b by omega)
    (lastRegeneration_measurable (a+2)).compl
    ((avoidOddReturns_measurable (a+2) n b (by omega)).inter (lastRegeneration_measurable b))]
  congr 1
  rw [avoidOddReturns_first_pair a n b (by omega),inter_assoc]

lemma returnCylinderTo_retains_past (a n b : ℕ) (hab : a+2*(n+1) ≤ b) (h : RawHistory a) :
    ∀ᵐ z ∂returnCylinderTo a n b hab h, rawPrefix (show a ≤ b by omega) z = h := by
  rw [returnCylinderTo,Kernel.restrict_apply]
  exact ae_restrict_of_ae (rawExtension_retains_prefix (by omega) h)

lemma returnCylinderTo_retains_coordinate (a n b : ℕ) (hab : a+2*(n+1) ≤ b)
    (h : RawHistory a) (i : Finset.Iic a) :
    ∀ᵐ z ∂returnCylinderTo a n b hab h,
      z ⟨i.1,Finset.mem_Iic.mpr (by have hi := Finset.mem_Iic.mp i.2; omega)⟩ = h i := by
  filter_upwards [returnCylinderTo_retains_past a n b hab h] with z hz
  exact congrFun hz i

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw

noncomputable def keepFirstEvenUpdate (x : FirstPairWitness × OddCost) : FirstPairWitness := (x.1.1,x.2)

lemma keepFirstEvenUpdate_measurable : Measurable keepFirstEvenUpdate :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

noncomputable def firstEvenReturnContinuation (n : ℕ) : Kernel FirstPairWitness FirstPairWitness :=
  (Kernel.id ×ₖ (firstReturn n).prodMkLeft EvenState).map keepFirstEvenUpdate

instance firstEvenReturnContinuation_isFiniteKernel (n : ℕ) : IsFiniteKernel (firstEvenReturnContinuation n) := by
  unfold firstEvenReturnContinuation
  infer_instance

lemma firstEvenReturnContinuation_apply (n : ℕ) (z : FirstPairWitness) {B : Set FirstPairWitness}
    (hB : MeasurableSet B) :
    firstEvenReturnContinuation n z B = firstReturn n z.2 {y | (z.1,y) ∈ B} := by
  rw [firstEvenReturnContinuation,Kernel.map_apply' _ keepFirstEvenUpdate_measurable _ hB,
    Kernel.prod_apply' _ _ _ (keepFirstEvenUpdate_measurable hB),Kernel.id_apply,lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (keepFirstEvenUpdate_measurable hB)

lemma firstEvenReturnContinuation_lintegral (n : ℕ) (z : FirstPairWitness)
    {F : FirstPairWitness → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂firstEvenReturnContinuation n z) = ∫⁻ y, F (z.1,y) ∂firstReturn n z.2 := by
  have he : firstEvenReturnContinuation n z = (firstReturn n z.2).map (fun y => (z.1,y)) := by
    ext B hB
    rw [firstEvenReturnContinuation_apply _ _ hB,
      Measure.map_apply (f := fun y : OddCost => (z.1,y)) (measurable_const.prodMk measurable_id) hB]
    rfl
  rw [he,lintegral_map (g := fun y : OddCost => (z.1,y)) hF (measurable_const.prodMk measurable_id)]

noncomputable def capturedFirstPair : Kernel OddCost FirstPairWitness :=
  pairWitnessKernel.restrict (returnSet_measurable.preimage measurable_snd)

noncomputable def killedFirstPair : Kernel OddCost FirstPairWitness :=
  pairWitnessKernel.restrict (returnSet_measurable.compl.preimage measurable_snd)

instance capturedFirstPair_isFiniteKernel : IsFiniteKernel capturedFirstPair := by
  unfold capturedFirstPair
  infer_instance

instance killedFirstPair_isFiniteKernel : IsFiniteKernel killedFirstPair := by
  unfold killedFirstPair
  infer_instance

noncomputable def sourceReturnTerm : ℕ → Kernel OddCost FirstPairWitness
  | 0 => capturedFirstPair
  | n+1 => firstEvenReturnContinuation n ∘ₖ killedFirstPair

instance sourceReturnTerm_isFiniteKernel (n : ℕ) : IsFiniteKernel (sourceReturnTerm n) := by
  cases n <;> unfold sourceReturnTerm <;> infer_instance

lemma capturedFirstPair_forget (z : OddCost) :
    (capturedFirstPair z).map Prod.snd = costCaptured z := by
  rw [capturedFirstPair,Kernel.restrict_apply,← Measure.restrict_map measurable_snd returnSet_measurable,
    pairWitness_forget,costCaptured,Kernel.restrict_apply]

lemma killedFirstPair_forget (z : OddCost) :
    (killedFirstPair z).map Prod.snd = costKilled z := by
  rw [killedFirstPair,Kernel.restrict_apply,← Measure.restrict_map measurable_snd returnSet_measurable.compl,
    pairWitness_forget,costKilled,Kernel.restrict_apply]

lemma firstEvenReturnContinuation_forget (n : ℕ) (z : FirstPairWitness) :
    (firstEvenReturnContinuation n z).map Prod.snd = firstReturn n z.2 := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,firstEvenReturnContinuation_apply _ _ (measurable_snd hB)]
  rfl

lemma sourceReturnTerm_forget (n : ℕ) (z : OddCost) :
    (sourceReturnTerm n z).map Prod.snd = firstReturn n z := by
  cases n with
  | zero =>
    have he : firstReturn 0 = costCaptured := Kernel.comp_id _
    rw [he]
    exact capturedFirstPair_forget z
  | succ n =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF measurable_snd,sourceReturnTerm,
      Kernel.lintegral_comp _ _ _ (g := fun y : FirstPairWitness => F y.2) (hF.comp measurable_snd)]
    have he (x : FirstPairWitness) : (∫⁻ y, F y.2 ∂firstEvenReturnContinuation n x) =
        ∫⁻ y, F y ∂firstReturn n x.2 := by
      rw [← firstEvenReturnContinuation_forget n x,lintegral_map hF measurable_snd]
    simp_rw [he]
    have hJ : Measurable (fun x : OddCost => ∫⁻ y, F y ∂firstReturn n x) := hF.lintegral_kernel
    rw [← lintegral_map (g := Prod.snd) hJ measurable_snd,killedFirstPair_forget,
      firstReturn_succ_comp,Kernel.lintegral_comp _ _ _ hF]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels

instance fullPairKilled_pow_isFiniteKernel (n : ℕ) : IsFiniteKernel (fullPairKilled^n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel CostState CostState); infer_instance
  | succ n ih => rw [pow_succ']; change IsFiniteKernel (fullPairKilled ∘ₖ (fullPairKilled^n)); infer_instance

instance fullPairReturn_isFiniteKernel (n : ℕ) : IsFiniteKernel (fullPairReturn n) := by
  unfold fullPairReturn
  infer_instance

noncomputable def returnPairReward (n : ℕ) (F : CostState × CostState → ℝ≥0∞) (p : CostState × CostState) : ℝ≥0∞ :=
  ∫⁻ y, F (p.1,y) ∂fullPairReturn n p.2

lemma returnPairReward_measurable (n : ℕ) {F : CostState × CostState → ℝ≥0∞} (hF : Measurable F) :
    Measurable (returnPairReward n F) := by
  let K : Kernel (CostState × CostState) CostState :=
    (fullPairReturn n).comap (Prod.snd : CostState × CostState → CostState) measurable_snd
  change Measurable (fun p : CostState × CostState => ∫⁻ y, F (p.1,y) ∂K p)
  exact Measurable.lintegral_kernel_prod_right' (κ := K)
    (f := fun x : (CostState × CostState) × CostState => F (x.1.1,x.2))
    (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

lemma sourceReturnTerm_succ_reward (n : ℕ) (z : OddCost) {F : CostState × CostState → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ y, F (pairTraceOfWitness z y) ∂sourceReturnTerm (n+1) z) =
      ∫⁻ p, returnPairReward n F (pairTraceOfWitness z p) ∂killedFirstPair z := by
  rw [sourceReturnTerm,Kernel.lintegral_comp _ _ _
    (g := fun y : FirstPairWitness => F (pairTraceOfWitness z y)) (hF.comp (pairTraceOfWitness_measurable z))]
  apply lintegral_congr
  intro p
  rw [firstEvenReturnContinuation_lintegral n p
    (F := fun y : FirstPairWitness => F (pairTraceOfWitness z y)) (hF.comp (pairTraceOfWitness_measurable z))]
  have hG : Measurable (fun y : CostState => F ((pairTraceOfWitness z p).1,y)) :=
    hF.comp measurable_prodMk_left
  rw [returnPairReward]
  change (∫⁻ y, F ((pairTraceOfWitness z p).1,embedOdd y) ∂NumberTheoryLean.CostReturnLaw.firstReturn n p.2) =
    ∫⁻ y, F ((pairTraceOfWitness z p).1,y) ∂fullPairReturn n (embedOdd p.2)
  rw [← firstReturn_fullPair_projection n p.2,
    lintegral_map (g := embedOdd) (f := fun y : CostState => F ((pairTraceOfWitness z p).1,y)) hG embedOdd_measurable]

lemma killedFirstPair_trace (z : OddCost) :
    (killedFirstPair z).map (pairTraceOfWitness z) =
      (fullPairTraceKernel (embedOdd z)).restrict (Prod.snd ⁻¹' regenerationSetᶜ) := by
  rw [killedFirstPair,Kernel.restrict_apply]
  change ((pairWitnessKernel z).restrict ((pairTraceOfWitness z) ⁻¹' (Prod.snd ⁻¹' regenerationSetᶜ))).map
    (pairTraceOfWitness z) = _
  rw [← Measure.restrict_map (pairTraceOfWitness_measurable z) (measurable_snd regenerationSet_measurable.compl),
    pairWitness_joint_full_trace]

lemma capturedFirstPair_trace (z : OddCost) :
    (capturedFirstPair z).map (pairTraceOfWitness z) =
      (fullPairTraceKernel (embedOdd z)).restrict (Prod.snd ⁻¹' regenerationSet) := by
  rw [capturedFirstPair,Kernel.restrict_apply]
  change ((pairWitnessKernel z).restrict ((pairTraceOfWitness z) ⁻¹' (Prod.snd ⁻¹' regenerationSet))).map
    (pairTraceOfWitness z) = _
  rw [← Measure.restrict_map (pairTraceOfWitness_measurable z) (measurable_snd regenerationSet_measurable),
    pairWitness_joint_full_trace]

lemma rawKilledFirstPair_trace (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    ((((rawExtension a (a+2)).restrict (lastRegeneration_measurable (a+2)).compl) h).map (nextPairEval a)) =
      (killedFirstPair z).map (pairTraceOfWitness z) := by
  rw [Kernel.restrict_apply]
  change ((rawExtension a (a+2) h).restrict ((nextPairEval a) ⁻¹' (Prod.snd ⁻¹' regenerationSetᶜ))).map
    (nextPairEval a) = _
  rw [← Measure.restrict_map (nextPairEval_measurable a) (measurable_snd regenerationSet_measurable.compl)]
  have he : (rawExtension a (a+2) h).map (nextPairEval a) = fullPairTraceKernel (rawLast a h) :=
    conditional_pair_trace a h
  rw [he,hz,killedFirstPair_trace]

lemma rawCapturedFirstPair_trace (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    ((((rawExtension a (a+2)).restrict (lastRegeneration_measurable (a+2))) h).map (nextPairEval a)) =
      (capturedFirstPair z).map (pairTraceOfWitness z) := by
  rw [Kernel.restrict_apply]
  change ((rawExtension a (a+2) h).restrict ((nextPairEval a) ⁻¹' (Prod.snd ⁻¹' regenerationSet))).map
    (nextPairEval a) = _
  rw [← Measure.restrict_map (nextPairEval_measurable a) (measurable_snd regenerationSet_measurable)]
  have he : (rawExtension a (a+2) h).map (nextPairEval a) = fullPairTraceKernel (rawLast a h) :=
    conditional_pair_trace a h
  rw [he,hz,capturedFirstPair_trace]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

noncomputable def rawCyclePairEval (a b : ℕ) (hab : a+1 ≤ b) (h : RawHistory b) : CostState × CostState :=
  (h ⟨a+1,Finset.mem_Iic.mpr hab⟩,rawLast b h)

lemma rawCyclePairEval_measurable (a b : ℕ) (hab : a+1 ≤ b) : Measurable (rawCyclePairEval a b hab) :=
  (measurable_pi_apply _).prodMk (rawLast_measurable b)

lemma returnCylinderTo_projection (a n b : ℕ) (hab : a+2*(n+1) ≤ b) (hb : b=a+2*(n+1)) :
    (returnCylinderTo a n b hab).map (rawLast b) =
      (fullPairReturn n).comap (rawLast a) (rawLast_measurable a) := by
  subst b
  exact firstReturnHistory_kernel_projection a n

lemma rawRemainder_pair_reward (a n b : ℕ) (hab : (a+2)+2*(n+1) ≤ b)
    (hb : b=(a+2)+2*(n+1)) (h : RawHistory (a+2))
    {F : CostState × CostState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F (rawCyclePairEval a b (by omega) y) ∂returnCylinderTo (a+2) n b hab h) =
      returnPairReward n F (nextPairEval a h) := by
  have hae := returnCylinderTo_retains_coordinate (a+2) n b hab h
    (⟨a+1,Finset.mem_Iic.mpr (by omega)⟩ : Finset.Iic (a+2))
  have heq : (fun y => F (rawCyclePairEval a b (by omega) y)) =ᵐ[returnCylinderTo (a+2) n b hab h]
      fun y => F ((nextPairEval a h).1,rawLast b y) := by
    filter_upwards [hae] with y hy
    change F (y ⟨a+1,_⟩,rawLast b y)=F (h ⟨a+1,_⟩,rawLast b y)
    rw [hy]
  rw [lintegral_congr_ae heq]
  have hG : Measurable (fun y : CostState => F ((nextPairEval a h).1,y)) := hF.comp measurable_prodMk_left
  rw [← lintegral_map (g := rawLast b) (f := fun y : CostState => F ((nextPairEval a h).1,y)) hG (rawLast_measurable b)]
  have hp := congrArg (fun K : Kernel (RawHistory (a+2)) CostState => K h)
    (returnCylinderTo_projection (a+2) n b hab hb)
  rw [Kernel.map_apply _ (rawLast_measurable b),Kernel.comap_apply] at hp
  rw [hp]
  rfl

theorem firstReturnHistory_joint (a n : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (firstReturnHistory a n h).map (rawCyclePairEval a (a+2*(n+1)) (by omega)) =
      (sourceReturnTerm n z).map (pairTraceOfWitness z) := by
  cases n with
  | zero =>
    change (firstReturnHistory a 0 h).map (nextPairEval a) = (capturedFirstPair z).map (pairTraceOfWitness z)
    rw [firstReturnHistory_zero]
    exact rawCapturedFirstPair_trace a h z hz
  | succ n =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (rawCyclePairEval_measurable _ _ _),
      lintegral_map hF (pairTraceOfWitness_measurable z),sourceReturnTerm_succ_reward n z hF]
    have hc : firstReturnHistory a (n+1) =
        returnCylinderTo a (n+1) (a+2*(n+2)) (by omega) := rfl
    rw [hc,returnCylinderTo_first_pair a n (a+2*(n+2)) le_rfl,
      Kernel.lintegral_comp _ _ _
        (g := fun y => F (rawCyclePairEval a (a+2*(n+2)) (by omega) y))
        (hF.comp (rawCyclePairEval_measurable a (a+2*(n+2)) (by omega)))]
    have hi (y : RawHistory (a+2)) :
        (∫⁻ w, F (rawCyclePairEval a (a+2*(n+2)) (by omega) w)
          ∂returnCylinderTo (a+2) n (a+2*(n+2)) (by omega) y) =
        returnPairReward n F (nextPairEval a y) :=
      rawRemainder_pair_reward a n _ (by omega) (by omega) y hF
    simp_rw [hi]
    rw [← lintegral_map (g := nextPairEval a) (returnPairReward_measurable n hF) (nextPairEval_measurable a),
      rawKilledFirstPair_trace a h z hz,
      lintegral_map (returnPairReward_measurable n hF) (pairTraceOfWitness_measurable z)]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
