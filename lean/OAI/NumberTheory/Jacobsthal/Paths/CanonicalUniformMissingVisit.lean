import OAI.NumberTheory.Jacobsthal.Estimates.ActualOddPairLink

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.InitialRegeneration
open NumberTheoryLean.KernelPotential

lemma oddConsecutiveContinue_power_embed (v H : ℝ) (n : ℕ) (z : OddCost) :
    (((oddConsecutiveContinue v H)^n) z).map embedOdd=
      ((consecutiveContinue v H)^n) (embedOdd z) := by
  exact supported_projection_power (oddConsecutiveContinue v H) (consecutiveContinue v H)
    (S := univ) MeasurableSet.univ (fun _ => Eventually.of_forall (fun _ => mem_univ _)) embedOdd_measurable
    (fun z _ => oddConsecutiveContinue_embed v H z) n z (mem_univ _)

theorem consecutiveMarkedHit_odd_mass (v H : ℝ) (z : OddCost) :
    consecutiveMarkedHit v H (embedOdd z) univ=oddConsecutiveHit v H z univ := by
  have (n : ℕ) : IsSFiniteKernel ((consecutiveContinue v H)^n) := kernel_power_sfinite _ n
  have (n : ℕ) : IsSFiniteKernel ((oddConsecutiveContinue v H)^n) := kernel_power_sfinite _ n
  rw [consecutiveMarkedHit,oddConsecutiveHit,potential,potential,Kernel.sum_apply' _ _ MeasurableSet.univ,
    Kernel.sum_apply' _ _ MeasurableSet.univ]
  apply tsum_congr
  intro n
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ,Kernel.comp_apply' _ _ _ MeasurableSet.univ,
    ← oddConsecutiveContinue_power_embed v H n z,
    lintegral_map ((consecutiveCapture v H).measurable_coe MeasurableSet.univ) embedOdd_measurable]
  apply lintegral_congr
  intro y
  exact (oddConsecutiveCapture_mass_embed v H y).symm

theorem consecutiveMarkedHit_after_regeneration (v H : ℝ) (z : OddCost) :
    consecutiveMarkedHit v H (embedOdd z) univ=
      ∫⁻ y, ordinaryMarkedHit v H y univ ∂hitOrReturn z := by
  rw [consecutiveMarkedHit_odd_mass,oddConsecutiveHit_eq_cycles,Kernel.comp_apply' _ _ _ MeasurableSet.univ]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.TransitionKernels
open NumberTheoryLean.InitialOddDraw NumberTheoryLean.InitialRegeneration

noncomputable def canonicalEvenPairVisitKernel (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) FiniteRawHistory :=
  canonicalPairVisitKernel (a+1) v H ∘ₖ rawExtension a (a+1)

instance canonicalEvenPairVisitKernel_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (canonicalEvenPairVisitKernel a v H) := by
  unfold canonicalEvenPairVisitKernel
  infer_instance

theorem canonicalEvenPairVisit_completion (a N : ℕ) (v H : ℝ) :
    extendFinitePrefix N ∘ₖ canonicalEvenPairVisitKernel a v H=
      (rawExtension a N).restrict (anyPairHit_measurable (a+1) N v H) := by
  rw [canonicalEvenPairVisitKernel,← Kernel.comp_assoc,canonicalPairVisit_completion,Kernel.comp_restrict]
  have he : rawExtension (a+1) N ∘ₖ rawExtension a (a+1)=rawExtension a N :=
    Kernel.partialTraj_comp_partialTraj' (X := fun _ => CostState) (κ := historyKernel) N (show a ≤ a+1 by omega)
  rw [he]

theorem canonicalEvenPairVisit_mass (a : ℕ) (v H : ℝ) (past : RawHistory a) (s : EvenState)
    (hs : rawLast a past=(Sum.inl s,0)) :
    canonicalEvenPairVisitKernel a v H past univ=ordinaryInitialHitMass s v H := by
  rw [canonicalEvenPairVisitKernel,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  simp_rw [canonicalPairVisit_mass]
  have hG : Measurable (fun z : CostState => consecutiveMarkedHit v H z univ) :=
    (consecutiveMarkedHit v H).measurable_coe MeasurableSet.univ
  rw [← lintegral_map (g := rawLast (a+1)) hG (rawLast_measurable (a+1)),
    rawFirstOdd_draw_law a past s hs,lintegral_map hG embedOdd_measurable]
  simp_rw [consecutiveMarkedHit_after_regeneration]
  rw [ordinaryInitialHitMass,delayedRegeneration,Kernel.lintegral_comp _ _ _
    ((ordinaryMarkedHit v H).measurable_coe MeasurableSet.univ)]

theorem canonicalEvenPairVisit_exponential (S : ℝ) : ∃ eta C eta0 B : ℝ,
    0 < eta ∧ 0 < C ∧ 0 < eta0 ∧ 0 ≤ B ∧ ∀ (a : ℕ) (past : RawHistory a) (s : EvenState),
      rawLast a past=(Sum.inl s,0) → s.1 ≤ S → ∀ v H : ℝ, 0 ≤ H →
        1-canonicalEvenPairVisitKernel a v H past univ ≤
          ENNReal.ofReal (C*Real.exp (-eta*H)+B*Real.exp (-eta0*v)) := by
  obtain ⟨eta,C,eta0,B,heta,hC,heta0,hB,h⟩ := ordinaryInitialHit_exponential S
  refine ⟨eta,C,eta0,B,heta,hC,heta0,hB,?_⟩
  intro a past s hs hS v H hH
  rw [canonicalEvenPairVisit_mass a v H past s hs]
  exact h s hS v H hH

theorem moving_canonical_even_visit {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ (a : ℕ) (past : RawHistory a) (s : EvenState),
        rawLast a past=(Sum.inl s,0) → 199/100 ≤ s.1 → s.1 ≤ 23/10 →
        1-canonicalEvenPairVisitKernel a (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) past univ ≤
          ENNReal.ofReal eps := by
  obtain ⟨rho,hrho,hMoving⟩ := moving_ordinary_marked_hit heps
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [hMoving K hK] with w hw
  refine ⟨hw.1,?_⟩
  intro r hr a past s hs hs0 hs1
  rw [canonicalEvenPairVisit_mass a _ _ past s hs]
  exact hw.2 r hr s hs0 hs1

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels

lemma extendFinitePrefix_total {α : Type*} [MeasurableSpace α] (N : ℕ)
    (K : Kernel α FiniteRawHistory) (x : α) :
    (extendFinitePrefix N ∘ₖ K) x univ=K x {q | q.1 ≤ N} := by
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  have hi : (fun q : FiniteRawHistory => extendFinitePrefix N q univ)=
      {q : FiniteRawHistory | q.1 ≤ N}.indicator (fun _ => (1:ℝ≥0∞)) := by
    funext q
    by_cases hq : q.1 ≤ N <;> simp [extendFinitePrefix,hq]
  rw [hi,lintegral_indicator (measurableSet_le finiteRawLength_measurable measurable_const)]
  simp only [lintegral_const,one_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter]

theorem canonicalEvenPairVisit_bounded_mass (a N : ℕ) (v H : ℝ) (past : RawHistory a) :
    canonicalEvenPairVisitKernel a v H past {q | q.1 ≤ N}=
      rawExtension a N past (anyPairHit (a+1) N v H) := by
  rw [← extendFinitePrefix_total N (canonicalEvenPairVisitKernel a v H) past,
    canonicalEvenPairVisit_completion,Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter]

lemma finite_history_length_exhausts (μ : Measure FiniteRawHistory) :
    Tendsto (fun N : ℕ => μ {q | q.1 ≤ N}) atTop (𝓝 (μ univ)) := by
  have hm : Monotone (fun N : ℕ => {q : FiniteRawHistory | q.1 ≤ N}) := by
    intro N M hNM q hq
    exact hq.trans hNM
  have hu : (⋃ N : ℕ, {q : FiniteRawHistory | q.1 ≤ N})=univ := by
    apply eq_univ_of_forall
    intro q
    exact mem_iUnion.mpr ⟨q.1,(show q.1 ≤ q.1 from le_rfl)⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hm
  rwa [hu] at ht

theorem canonical_even_hit_probability_limit (a : ℕ) (v H : ℝ) (past : RawHistory a) (s : EvenState)
    (hs : rawLast a past=(Sum.inl s,0)) :
    Tendsto (fun N : ℕ => rawExtension a N past (anyPairHit (a+1) N v H)) atTop
      (𝓝 (ordinaryInitialHitMass s v H)) := by
  have ht := finite_history_length_exhausts (canonicalEvenPairVisitKernel a v H past)
  simp_rw [canonicalEvenPairVisit_bounded_mass,canonicalEvenPairVisit_mass a v H past s hs] at ht
  exact ht

theorem finitePathMeasure_marked_hit_limit (s : EvenState) (v H : ℝ) :
    Tendsto (fun N : ℕ => finitePathMeasure (Sum.inl s) N (anyPairHit 1 N v H)) atTop
      (𝓝 (ordinaryInitialHitMass s v H)) := by
  exact canonical_even_hit_probability_limit 0 v H (fun _ => (Sum.inl s,0)) s rfl

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.ArrivalKernelGeometry NumberTheoryLean.OccupationBoundaries

lemma pair_no_future_hit_of_bad_inputs (a N M : ℕ) (hNM : N ≤ M) (v H : ℝ)
    (past : RawHistory N) (hNo : past ∉ anyPairHit a N v H)
    (hBad : ∀ᵐ y ∂rawExtension N M past, ∀ i : Finset.Iic M, N ≤ i.1 →
      y i ∉ regenerativeCostWindow v H) :
    ∀ᵐ y ∂rawExtension N M past, y ∉ anyPairHit a M v H := by
  filter_upwards [hBad,rawExtension_retains_prefix hNM past] with y hy hp
  intro hHit
  obtain ⟨k,hk,hT⟩ := hHit
  by_cases hj : a+2*k+1 ≤ N
  · have hSmall : rawPrefix hNM y ∈ pairHitTest a k N hj v H := by
      change y ∈ rawPrefix hNM ⁻¹' pairHitTest a k N hj v H
      rw [pairHitTest_prefix]
      exact hT
    rw [hp] at hSmall
    exact hNo ⟨k,hj,hSmall⟩
  · exact hy ⟨a+2*k,Finset.mem_Iic.mpr (by omega)⟩ (show N ≤ a+2*k by omega) ⟨hT.1,hT.2.2⟩

lemma regeneration_ratio_le_three (z : CostState) (hz : z ∈ regenerationSet) : stateRatio z.1 ≤ 3 := by
  rcases z with ⟨s,T⟩
  cases s with
  | inl e => exact False.elim (regeneration_even e T hz)
  | inr o => exact hz

lemma eligible_input_large_exponent {r b0 b1 : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (z : CostState) (hz : z ∈ regenerativeCostWindow (Real.log (r/b1)) (Real.log (b1/(10*b0)))) :
    2*b0 < currentExponent (Real.log r) z := by
  have hGap := (marked_cost_window hr hb0 hb1 z.2).mpr hz.2
  have hRatio := regeneration_ratio_le_three z hz.1
  unfold currentExponent
  rw [gapValue_log_eq_gapAt hr]
  apply (lt_div_iff₀ (stateRatio_pos z.1)).mpr
  have hm := mul_le_mul_of_nonneg_left hRatio (show 0 ≤ 2*b0 by positivity)
  nlinarith [hGap.1]

theorem low_gap_no_future_pair_hit {r b0 b1 : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (a N M : ℕ) (hNM : N ≤ M) (past : RawHistory N)
    (hNo : past ∉ anyPairHit a N (Real.log (r/b1)) (Real.log (b1/(10*b0))))
    (hLow : gapAt r (rawLast N past).2 < 10*b0) :
    ∀ᵐ y ∂rawExtension N M past, y ∉ anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))) := by
  apply pair_no_future_hit_of_bad_inputs a N M hNM _ _ past hNo
  filter_upwards [rawExtension_increasingCosts N M past,rawExtension_retains_prefix hNM past] with y hI hp
  have he := congrFun hp (⟨N,by simp⟩ : Finset.Iic N)
  change y ⟨N,Finset.mem_Iic.mpr hNM⟩=rawLast N past at he
  intro i hNi hGood
  have hCost := hI ⟨N,Finset.mem_Iic.mpr hNM⟩ i le_rfl hNi
  have hGap := gapAt_antitone_cost hr.le hCost
  rw [he] at hGap
  have hWindow := (marked_cost_window hr hb0 hb1 (y i).2).mpr hGood.2
  exact (not_lt_of_ge (hWindow.1.trans hGap)) hLow

theorem cutoff_no_future_pair_hit {r b0 b1 ell : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hell : ell < 2*b0) (a N M : ℕ) (hNM : N ≤ M) (past : RawHistory N)
    (hNo : past ∉ anyPairHit a N (Real.log (r/b1)) (Real.log (b1/(10*b0))))
    (hCut : currentExponent (Real.log r) (rawLast N past) ≤ ell) :
    ∀ᵐ y ∂rawExtension N M past, y ∉ anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))) := by
  apply pair_no_future_hit_of_bad_inputs a N M hNM _ _ past hNo
  have hF : Measurable (fun z => -currentExponent (Real.log r) z) := (currentExponent_measurable _).neg
  have hStep (z : CostState) : ∀ᵐ y ∂costKernel z, -currentExponent (Real.log r) z ≤ -currentExponent (Real.log r) y := by
    filter_upwards [costKernel_exponent_nonincreasing (Real.log r) z] with y hy
    exact neg_le_neg hy
  filter_upwards [rawExtension_scalarIncreasing (fun z => -currentExponent (Real.log r) z) hF hStep N M past,
    rawExtension_retains_prefix hNM past] with y hI hp
  change ∀ i j : Finset.Iic M, N ≤ i.1 → i.1 ≤ j.1 →
    -currentExponent (Real.log r) (y i) ≤ -currentExponent (Real.log r) (y j) at hI
  have he := congrFun hp (⟨N,by simp⟩ : Finset.Iic N)
  change y ⟨N,Finset.mem_Iic.mpr hNM⟩=rawLast N past at he
  intro i hNi hGood
  have hX := hI ⟨N,Finset.mem_Iic.mpr hNM⟩ i le_rfl hNi
  rw [he] at hX
  have hLarge := eligible_input_large_exponent hr hb0 hb1 (y i) hGood
  linarith

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.ArrivalKernelGeometry

noncomputable def closedNoHitEvent (a N : ℕ) (r b0 b1 ell : ℝ) : Set (RawHistory N) :=
  (anyPairHit a N (Real.log (r/b1)) (Real.log (b1/(10*b0))))ᶜ ∩
    {past | gapAt r (rawLast N past).2 < 10*b0 ∨ currentExponent (Real.log r) (rawLast N past) ≤ ell}

lemma closedNoHitEvent_measurable (a N : ℕ) (r b0 b1 ell : ℝ) :
    MeasurableSet (closedNoHitEvent a N r b0 b1 ell) := by
  have hGap : Measurable (fun h : RawHistory N => gapAt r (rawLast N h).2) :=
    measurable_const.mul (Real.measurable_exp.comp ((measurable_snd.comp (rawLast_measurable N)).neg))
  exact (anyPairHit_measurable a N _ _).compl.inter
    ((measurableSet_lt hGap measurable_const).union
      (measurableSet_le ((currentExponent_measurable _).comp (rawLast_measurable N)) measurable_const))

lemma closedNoHitEvent_future {r b0 b1 ell : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hell : ell < 2*b0) (a N M : ℕ) (hNM : N ≤ M) (past : RawHistory N)
    (hp : past ∈ closedNoHitEvent a N r b0 b1 ell) :
    ∀ᵐ y ∂rawExtension N M past,
      y ∉ anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))) := by
  rcases hp.2 with hLow | hCut
  · exact low_gap_no_future_pair_hit hr hb0 hb1 a N M hNM past hp.1 hLow
  · exact cutoff_no_future_pair_hit hr hb0 hb1 hell a N M hNM past hp.1 hCut

theorem closedNoHitEvent_mass_future {r b0 b1 ell : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hell : ell < 2*b0) (s a N M : ℕ) (hsN : s ≤ N) (hNM : N ≤ M) (past : RawHistory s) :
    rawExtension s N past (closedNoHitEvent a N r b0 b1 ell) ≤
      rawExtension s M past (anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))))ᶜ := by
  let E := closedNoHitEvent a N r b0 b1 ell
  let C := (anyPairHit a M (Real.log (r/b1)) (Real.log (b1/(10*b0))))ᶜ
  have hE : MeasurableSet E := closedNoHitEvent_measurable a N r b0 b1 ell
  have hC : MeasurableSet C := (anyPairHit_measurable a M _ _).compl
  have he : rawExtension N M ∘ₖ rawExtension s N=rawExtension s M :=
    Kernel.partialTraj_comp_partialTraj hsN hNM
  change rawExtension s N past E ≤ rawExtension s M past C
  rw [← he,Kernel.comp_apply' _ _ _ hC]
  calc
    _ = ∫⁻ h, E.indicator (fun _ => (1:ℝ≥0∞)) h ∂rawExtension s N past := by
      rw [lintegral_indicator hE]
      simp
    _ ≤ _ := by
      apply lintegral_mono
      intro h
      by_cases hh : h ∈ E
      · have hStay := closedNoHitEvent_future hr hb0 hb1 hell a N M hNM h hh
        have hMass := (ae_mem_iff_measure_eq hC.nullMeasurableSet).mp hStay
        rw [measure_univ] at hMass
        rw [indicator_of_mem hh]
        change 1 ≤ rawExtension N M h C
        exact hMass.symm.le
      · rw [indicator_of_notMem hh]
        exact zero_le

theorem canonical_closed_nohit_le_failure {r b0 b1 ell : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1)
    (hell : ell < 2*b0) (s : EvenState) (N : ℕ) :
    finitePathMeasure (Sum.inl s) N (closedNoHitEvent 1 N r b0 b1 ell) ≤
      1-ordinaryInitialHitMass s (Real.log (r/b1)) (Real.log (b1/(10*b0))) := by
  let C := finitePathMeasure (Sum.inl s) N (closedNoHitEvent 1 N r b0 b1 ell)
  let I := ordinaryInitialHitMass s (Real.log (r/b1)) (Real.log (b1/(10*b0)))
  have hLimit := (finitePathMeasure_marked_hit_limit s (Real.log (r/b1)) (Real.log (b1/(10*b0)))).const_add C
  have hTail : ∀ᶠ M : ℕ in atTop,
      C+finitePathMeasure (Sum.inl s) M (anyPairHit 1 M (Real.log (r/b1)) (Real.log (b1/(10*b0)))) ≤ 1 := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    have hle := closedNoHitEvent_mass_future hr hb0 hb1 hell 0 1 N M (Nat.zero_le _) hNM
      (fun _ => (Sum.inl s,0))
    calc
      _ ≤ finitePathMeasure (Sum.inl s) M (anyPairHit 1 M (Real.log (r/b1)) (Real.log (b1/(10*b0))))ᶜ+
          finitePathMeasure (Sum.inl s) M (anyPairHit 1 M (Real.log (r/b1)) (Real.log (b1/(10*b0)))) :=
        add_le_add hle le_rfl
      _ = 1 := by
        rw [add_comm,measure_add_measure_compl (anyPairHit_measurable 1 M _ _),measure_univ]
  have hAdd : C+I ≤ 1 := le_of_tendsto hLimit hTail
  have hI : I ≠ ∞ := ne_top_of_le_ne_top (by simp : (1:ℝ≥0∞) ≠ ∞) (ordinaryInitialHitMass_le_one s _ _)
  exact ENNReal.le_sub_of_add_le_right hI hAdd

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels

theorem canonical_closed_nohit_exponential (S : ℝ) : ∃ eta C eta0 B : ℝ,
    0 < eta ∧ 0 < C ∧ 0 < eta0 ∧ 0 ≤ B ∧
    ∀ (r b0 b1 ell : ℝ), 0 < r → 0 < b0 → 0 < b1 → 10*b0 ≤ b1 → ell < 2*b0 →
      ∀ (s : EvenState), s.1 ≤ S → ∀ N : ℕ,
        finitePathMeasure (Sum.inl s) N (closedNoHitEvent 1 N r b0 b1 ell) ≤
          ENNReal.ofReal (C*Real.exp (-eta*Real.log (b1/(10*b0)))+
            B*Real.exp (-eta0*Real.log (r/b1))) := by
  obtain ⟨eta,C,eta0,B,heta,hC,heta0,hB,hBound⟩ := ordinaryInitialHit_exponential S
  refine ⟨eta,C,eta0,B,heta,hC,heta0,hB,?_⟩
  intro r b0 b1 ell hr hb0 hb1 hWindow hell s hS N
  have hRatio : 1 ≤ b1/(10*b0) := (le_div_iff₀ (by positivity : 0 < 10*b0)).mpr (by linarith)
  exact (canonical_closed_nohit_le_failure hr hb0 hb1 hell s N).trans
    (hBound s hS _ _ (Real.log_nonneg hRatio))

lemma moving_cutoff_one {K : ℝ} (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ 1 < 2*(K*(Real.log w)^2) := by
  filter_upwards [eventually_ge_atTop (max (3:ℝ) (Real.exp (1+1/K)))] with w hw
  have hw3 : 3 ≤ w := (le_max_left _ _).trans hw
  have hw0 : 0 < w := by linarith
  have hL : 1+1/K ≤ Real.log w := (Real.le_log_iff_exp_le hw0).mpr ((le_max_right _ _).trans hw)
  have hOne : 1 ≤ Real.log w := by have hi : 0 < 1/K := one_div_pos.mpr hK; linarith
  have hMul := mul_le_mul_of_nonneg_left hL hK.le
  have hEq : K*(1+1/K)=K+1 := by field_simp [hK.ne']
  rw [hEq] at hMul
  have hSq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hMulSq := mul_le_mul_of_nonneg_left hSq hK.le
  refine ⟨hw3,?_⟩
  nlinarith

theorem moving_canonical_missing_visit {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ s : EvenState,
        199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
        finitePathMeasure (Sum.inl s) N
          (closedNoHitEvent 1 N r (K*(Real.log w)^2) (rho*K*(Real.log w)^2) 1) ≤ ENNReal.ofReal eps := by
  obtain ⟨rho,hrho,hMoving⟩ := moving_ordinary_marked_hit heps
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [hMoving K hK,moving_cutoff_one hK] with w hw hCut
  refine ⟨hw.1,?_⟩
  intro r hr s hs0 hs1 N
  have hw0 : 0 < w := by linarith [hw.1]
  have hr0 : 0 < r := hw0.trans_le hr
  have hlog : 0 < Real.log w := Real.log_pos (by linarith [hw.1])
  let b0 := K*(Real.log w)^2
  have hb0 : 0 < b0 := by dsimp [b0]; positivity
  have hrho0 : 0 < rho := by linarith
  have hb1 : 0 < rho*b0 := mul_pos hrho0 hb0
  have he : rho*b0=rho*K*(Real.log w)^2 := by dsimp [b0]; ring
  have hBound := canonical_closed_nohit_le_failure hr0 hb0 hb1 hCut.2 s N
  rw [proportional_window_width hrho0 hb0,he] at hBound
  exact hBound.trans (hw.2 r hr s hs0 hs1)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
