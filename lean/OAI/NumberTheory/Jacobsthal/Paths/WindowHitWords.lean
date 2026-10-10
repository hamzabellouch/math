import OAI.NumberTheory.Jacobsthal.Probability.OrdinaryMarkedWindow

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.PairedCostGrouping

noncomputable def allowedCycleCosts (b : Bool) (v H : ℝ) : Set ℝ :=
  if b then (Icc v (v+H))ᶜ else univ

lemma allowedCycleCosts_measurable (b : Bool) (v H : ℝ) : MeasurableSet (allowedCycleCosts b v H) := by
  cases b <;> simp [allowedCycleCosts]

noncomputable def hitWordEvent : (w : List Bool) → (v H : ℝ) → Set (CycleWordSignature (w++[true]).length)
  | [], v, H => {s | s.1.1 ∈ Icc v (v+H)}
  | b::w, v, H => {s | s.1.1 ∈ allowedCycleCosts b v H ∧ s.2 ∈ hitWordEvent w v H}

lemma hitWordEvent_measurable (w : List Bool) : ∀ v H, MeasurableSet (hitWordEvent w v H) := by
  induction w with
  | nil => intro v H; exact measurableSet_Icc.preimage (measurable_fst.comp measurable_fst)
  | cons b w ih =>
    intro v H
    exact ((allowedCycleCosts_measurable b v H).preimage (measurable_fst.comp measurable_fst)).inter
      ((ih v H).preimage measurable_snd)

noncomputable def sourceHitWordMass (w : List Bool) (v H : ℝ) (z : OddCost) : ℝ≥0∞ :=
  sourceMarkedWordKernel (w++[true]) z (hitWordEvent w v H)

lemma sourceHitWordMass_measurable (w : List Bool) (v H : ℝ) : Measurable (sourceHitWordMass w v H) :=
  (sourceMarkedWordKernel (w++[true])).measurable_coe (hitWordEvent_measurable w v H)

lemma sourceHitWordMass_nil (v H : ℝ) (z : OddCost) :
    sourceHitWordMass [] v H z=ordinaryWindowCapture v H z univ := by
  have he := congrArg (fun μ : Measure ℝ => μ (Icc v (v+H))) (sourceLookahead_cost_law [] true z)
  rw [Measure.map_apply (lookaheadInputCost_measurable [] true) measurableSet_Icc,
    Measure.map_apply measurable_snd measurableSet_Icc] at he
  change sourceHitWordMass [] v H z = _ at he
  have hc : ordinaryWindowCapture v H z univ =
      ((branchWordKernel [] z).withDensity (fun y => cycleBranchKernel true y univ))
        (Prod.snd ⁻¹' Icc v (v+H)) := by
    rw [ordinaryWindowCapture,Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter,
      markInputWeightKernel,Kernel.withDensity_apply _ (f := fun _ z : OddCost => nextMarkWeight z)
        (nextMarkWeight_measurable.comp measurable_snd),Kernel.id_apply]
    rfl
  exact he.trans hc.symm

lemma sourceHitWordMass_indicator (w : List Bool) (v H : ℝ) (z : OddCost) :
    sourceHitWordMass w v H z =
      ∫⁻ s, (hitWordEvent w v H).indicator (fun _ => (1:ℝ≥0∞)) s ∂sourceMarkedWordKernel (w++[true]) z := by
  rw [lintegral_indicator (hitWordEvent_measurable w v H)]
  simp [sourceHitWordMass]

lemma sourceHitWordMass_cons (b : Bool) (w : List Bool) (v H : ℝ) (z : OddCost) :
    sourceHitWordMass (b::w) v H z =
      if z.2 ∈ allowedCycleCosts b v H then ∫⁻ y, sourceHitWordMass w v H y ∂cycleBranchKernel b z else 0 := by
  rw [sourceHitWordMass_indicator]
  change (∫⁻ s : CycleWordSignature (b::(w++[true])).length,
    (hitWordEvent (b::w) v H).indicator (fun _ => (1:ℝ≥0∞)) s ∂sourceMarkedWordKernel (b::(w++[true])) z) = _
  rw [sourceMarkedWord_cons_lintegral b (w++[true]) z
    (F := (hitWordEvent (b::w) v H).indicator (fun _ => (1:ℝ≥0∞)))
    (measurable_const.indicator (hitWordEvent_measurable (b::w) v H))]
  by_cases hz : z.2 ∈ allowedCycleCosts b v H
  · rw [ite_eq_left hz]
    have hi (y : SourceCycleWitness) (s : CycleWordSignature (w++[true]).length) :
        (hitWordEvent (b::w) v H).indicator (fun _ => (1:ℝ≥0∞)) (sourceCycleInputSignature z y,s) =
          (hitWordEvent w v H).indicator (fun _ => (1:ℝ≥0∞)) s := by
      simp only [Set.indicator_apply,hitWordEvent,mem_ofPred_eq,sourceCycleInputSignature,hz,true_and]
    simp_rw [hi,← sourceHitWordMass_indicator]
    rw [← lintegral_map (g := fun y : SourceCycleWitness => y.2.2) (sourceHitWordMass_measurable w v H)
      (measurable_snd.comp measurable_snd),sourceBranchWitness_endpoint]
  · rw [ite_eq_right hz]
    have hi (y : SourceCycleWitness) (s : CycleWordSignature (w++[true]).length) :
        (hitWordEvent (b::w) v H).indicator (fun _ => (1:ℝ≥0∞)) (sourceCycleInputSignature z y,s) = 0 := by
      simp only [Set.indicator_apply,hitWordEvent,mem_ofPred_eq,sourceCycleInputSignature,hz,false_and,ite_false]
    simp_rw [hi,lintegral_zero]

noncomputable def rawHitWordKernel (a : ℕ) (w : List Bool) (v H : ℝ) :
    Kernel (RawHistory a) (RawCycleWordTrace a (w++[true]).length) :=
  (rawMarkedWordKernel a (w++[true])).restrict
    ((hitWordEvent_measurable w v H).preimage (rawCycleWordSignature_measurable _ a))

instance rawHitWordKernel_isFiniteKernel (a : ℕ) (w : List Bool) (v H : ℝ) : IsFiniteKernel (rawHitWordKernel a w v H) := by
  unfold rawHitWordKernel
  infer_instance

theorem rawHitWord_mass (a : ℕ) (w : List Bool) (v H : ℝ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) : rawHitWordKernel a w v H h univ=sourceHitWordMass w v H z := by
  rw [rawHitWordKernel,Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter,
    ← Measure.map_apply (rawCycleWordSignature_measurable _ a) (hitWordEvent_measurable w v H),
    rawMarkedWord_signature (w++[true]) a h z hz]
  rfl

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
