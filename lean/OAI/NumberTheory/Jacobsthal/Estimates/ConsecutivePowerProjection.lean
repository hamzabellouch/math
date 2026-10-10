import OAI.NumberTheory.Jacobsthal.Paths.ConsecutivePairStop

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures

noncomputable def historyGoodInput (a : ℕ) (v H : ℝ) : Set (RawHistory a) :=
  rawLast a ⁻¹' regenerativeCostWindow v H

lemma historyGoodInput_measurable (a : ℕ) (v H : ℝ) : MeasurableSet (historyGoodInput a v H) :=
  (regenerativeCostWindow_measurable v H).preimage (rawLast_measurable a)

lemma pairHitTest_first_eq (a : ℕ) (v H : ℝ) :
    pairHitTest a 0 (a+1) (by omega) v H =
      (rawPrefix (show a ≤ a+1 by omega) ⁻¹' historyGoodInput a v H) ∩ firstPrefixMarkEvent a true := by
  ext h
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  constructor
  · rintro ⟨hR,hM,hW⟩
    exact ⟨⟨hR,hW⟩,hM⟩
  · rintro ⟨⟨hR,hW⟩,hM⟩
    exact ⟨hR,hM,hW⟩

theorem pairStoppedHistory_zero_input_filter (a : ℕ) (v H : ℝ) :
    pairStoppedHistory a 0 v H=
      ((rawExtension a (a+1)).restrict (firstPrefixMarkEvent_measurable a true)) ∘ₖ
        stateFilter (historyGoodInput_measurable a v H) := by
  rw [pairStoppedHistory_zero]
  have he := restriction_comp_of_retained_prefix (Kernel.id : Kernel (RawHistory a) (RawHistory a))
    (rawExtension a (a+1)) (rawPrefix_measurable (show a ≤ a+1 by omega))
    (rawExtension_retains_prefix (show a ≤ a+1 by omega))
    (historyGoodInput_measurable a v H) (firstPrefixMarkEvent_measurable a true)
  rw [Kernel.comp_id] at he
  ext past S hS
  have heS := congrArg (fun K : Kernel (RawHistory a) (RawHistory (a+1)) => K past S) he
  rw [Kernel.restrict_apply' _ _ _ hS] at heS
  rw [Kernel.restrict_apply' _ _ _ hS,pairHitTest_first_eq]
  exact heS

theorem canonical_capture_projection (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    (pairStoppedHistory a 0 v H past).map (rawLast (a+1))=consecutiveCapture v H (rawLast a past) := by
  rw [pairStoppedHistory_zero_input_filter,stateFilter_input,consecutiveCapture,stateFilter_input]
  by_cases hp : rawLast a past ∈ regenerativeCostWindow v H
  · have hh : past ∈ historyGoodInput a v H := hp
    rw [ite_eq_left hh,ite_eq_left hp,Kernel.restrict_apply,Kernel.restrict_apply]
    change ((rawExtension a (a+1) past).restrict ((rawLast (a+1)) ⁻¹' markedArrival)).map (rawLast (a+1))=_
    rw [← Measure.restrict_map (rawLast_measurable (a+1)) markedArrival_measurable,rawExtension_last_step]
  · have hh : past ∉ historyGoodInput a v H := hp
    rw [ite_eq_right hh,ite_eq_right hp,Measure.map_zero]

noncomputable def firstNoHitHistory (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory (a+1)) :=
  (rawExtension a (a+1)).restrict (pairHitTest_measurable a 0 (a+1) (by omega) v H).compl

instance firstNoHitHistory_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (firstNoHitHistory a v H) := by
  unfold firstNoHitHistory
  infer_instance

lemma firstHistory_partition (a : ℕ) (v H : ℝ) :
    pairStoppedHistory a 0 v H+firstNoHitHistory a v H=rawExtension a (a+1) := by
  ext past S hS
  rw [_root_.add_apply,Measure.add_apply,pairStoppedHistory_zero,firstNoHitHistory,
    Kernel.restrict_apply,Kernel.restrict_apply,← Measure.add_apply,
    Measure.restrict_add_restrict_compl (pairHitTest_measurable a 0 (a+1) (by omega) v H)]

theorem canonical_first_continue_projection (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    (firstNoHitHistory a v H past).map (rawLast (a+1))=consecutiveFirstContinue v H (rawLast a past) := by
  have hPart := congrArg (fun K : Kernel (RawHistory a) (RawHistory (a+1)) =>
    (K past).map (rawLast (a+1))) (firstHistory_partition a v H)
  rw [_root_.add_apply,Measure.map_add _ _ (rawLast_measurable (a+1)),
    canonical_capture_projection,rawExtension_last_step] at hPart
  have hOther := congrArg (fun K : Kernel CostState CostState => K (rawLast a past)) (consecutive_first_partition v H)
  rw [_root_.add_apply] at hOther
  ext S _hS
  have he := congrArg (fun μ : Measure CostState => μ S) (hPart.trans hOther.symm)
  simp only [Measure.add_apply] at he
  exact (ENNReal.add_right_inj (measure_ne_top (consecutiveCapture v H (rawLast a past)) S)).mp he

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

noncomputable def noHitPairHistory (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory (a+2)) :=
  (rawExtension a (a+2)).restrict (pairHitTest_measurable a 0 (a+2) (by omega) v H).compl

instance noHitPairHistory_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (noHitPairHistory a v H) := by
  unfold noHitPairHistory
  infer_instance

theorem noHitPairHistory_factor (a : ℕ) (v H : ℝ) :
    noHitPairHistory a v H=rawExtension (a+1) (a+2) ∘ₖ firstNoHitHistory a v H := by
  unfold noHitPairHistory firstNoHitHistory
  have he := rawExtension_restrict_comp (show a ≤ a+1 by omega) (show a+1 ≤ a+2 by omega)
    (pairHitTest_measurable a 0 (a+1) (by omega) v H).compl MeasurableSet.univ
  rw [Kernel.restrict_univ] at he
  ext past S hS
  have heS := congrArg (fun K : Kernel (RawHistory a) (RawHistory (a+2)) => K past S) he
  rw [Kernel.restrict_apply' _ _ _ hS] at heS
  rw [Kernel.restrict_apply' _ _ _ hS]
  have hSet : (rawPrefix (show a+1 ≤ a+2 by omega) ⁻¹' (pairHitTest a 0 (a+1) (by omega) v H)ᶜ) ∩ univ=
      (pairHitTest a 0 (a+2) (by omega) v H)ᶜ := by
    rw [inter_univ,preimage_compl,pairHitTest_prefix]
  rw [hSet] at heS
  exact heS

theorem canonical_pair_continue_projection (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    (noHitPairHistory a v H past).map (rawLast (a+2))=consecutiveContinue v H (rawLast a past) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (rawLast_measurable (a+2)),noHitPairHistory_factor,
    Kernel.lintegral_comp _ _ _ (g := fun h => F (rawLast (a+2) h)) (hF.comp (rawLast_measurable (a+2)))]
  have he (h : RawHistory (a+1)) :
      (∫⁻ y, F (rawLast (a+2) y) ∂rawExtension (a+1) (a+2) h)=∫⁻ z, F z ∂costKernel (rawLast (a+1) h) := by
    rw [← lintegral_map (g := rawLast (a+2)) hF (rawLast_measurable (a+2)),rawExtension_last_step]
  simp_rw [he]
  have hG : Measurable (fun z : CostState => ∫⁻ y, F y ∂costKernel z) := hF.lintegral_kernel
  rw [← lintegral_map (g := rawLast (a+1)) hG (rawLast_measurable (a+1)),canonical_first_continue_projection,
    consecutiveContinue,Kernel.lintegral_comp _ _ _ hF]

lemma shifted_pair_continue_projection (a n b : ℕ) (hb : b=(a+2*n)+2) (v H : ℝ)
    (past : RawHistory (a+2*n)) :
    (((rawExtension (a+2*n) b).restrict
      (pairHitTest_measurable a n b (by omega) v H).compl) past).map (rawLast b)=
        consecutiveContinue v H (rawLast (a+2*n) past) := by
  subst b
  exact canonical_pair_continue_projection (a+2*n) v H past

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

theorem pairSurvivingHistory_projection (a n : ℕ) (v H : ℝ) (past : RawHistory a) :
    (pairSurvivingHistory a n v H past).map (rawLast (a+2*n))=
      ((consecutiveContinue v H)^n) (rawLast a past) := by
  have (m : ℕ) : IsSFiniteKernel ((consecutiveContinue v H)^m) := kernel_power_sfinite _ m
  induction n with
  | zero =>
    rw [pairSurvivingHistory_zero]
    change (Measure.dirac past).map (rawLast a)=Measure.dirac (rawLast a past)
    exact Measure.map_dirac' (rawLast_measurable a) past
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF (rawLast_measurable _),pairSurvivingHistory_succ,
      Kernel.lintegral_comp _ _ _ (g := fun h => F (rawLast (a+2*(n+1)) h)) (hF.comp (rawLast_measurable _))]
    have he (h : RawHistory (a+2*n)) :
        (∫⁻ y, F (rawLast (a+2*(n+1)) y) ∂((rawExtension (a+2*n) (a+2*(n+1))).restrict
          (pairHitTest_measurable a n (a+2*(n+1)) (by omega) v H).compl) h)=
          ∫⁻ z, F z ∂consecutiveContinue v H (rawLast (a+2*n) h) := by
      rw [← lintegral_map (g := rawLast (a+2*(n+1))) hF (rawLast_measurable _),
        shifted_pair_continue_projection a n (a+2*(n+1)) (by omega) v H h]
    simp_rw [he]
    have hG : Measurable (fun z : CostState => ∫⁻ y, F y ∂consecutiveContinue v H z) := hF.lintegral_kernel
    rw [← lintegral_map (g := rawLast (a+2*n)) hG (rawLast_measurable _),ih,pow_succ']
    change (∫⁻ z, ∫⁻ y, F y ∂consecutiveContinue v H z ∂((consecutiveContinue v H)^n) (rawLast a past))=
      ∫⁻ y, F y ∂(consecutiveContinue v H ∘ₖ ((consecutiveContinue v H)^n)) (rawLast a past)
    exact (Kernel.lintegral_comp _ _ _ hF).symm

theorem pairStoppedHistory_projection (a n : ℕ) (v H : ℝ) (past : RawHistory a) :
    (pairStoppedHistory a n v H past).map (rawLast (a+2*n+1))=
      (consecutiveCapture v H ∘ₖ ((consecutiveContinue v H)^n)) (rawLast a past) := by
  have : IsSFiniteKernel ((consecutiveContinue v H)^n) := kernel_power_sfinite _ n
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (rawLast_measurable _),pairStoppedHistory_factor,
    Kernel.lintegral_comp _ _ _ (g := fun h => F (rawLast (a+2*n+1) h)) (hF.comp (rawLast_measurable _))]
  have he (h : RawHistory (a+2*n)) :
      (∫⁻ y, F (rawLast (a+2*n+1) y) ∂((rawExtension (a+2*n) (a+2*n+1)).restrict
        (pairHitTest_measurable a n (a+2*n+1) le_rfl v H)) h)=
        ∫⁻ z, F z ∂consecutiveCapture v H (rawLast (a+2*n) h) := by
    have hP := canonical_capture_projection (a+2*n) v H h
    rw [pairStoppedHistory_zero] at hP
    rw [← lintegral_map (g := rawLast (a+2*n+1)) hF (rawLast_measurable _)]
    exact congrArg (fun μ : Measure CostState => ∫⁻ z, F z ∂μ) hP
  simp_rw [he]
  have hG : Measurable (fun z : CostState => ∫⁻ y, F y ∂consecutiveCapture v H z) := hF.lintegral_kernel
  rw [← lintegral_map (g := rawLast (a+2*n)) hG (rawLast_measurable _),
    pairSurvivingHistory_projection,Kernel.lintegral_comp _ _ _ hF]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
