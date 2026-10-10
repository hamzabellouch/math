import OAI.NumberTheory.Jacobsthal.Probability.MarkedCostSublaws

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.RegenerationTails

lemma completedMarked_ae_regeneration (z : OddCost) :
    ∀ᵐ y ∂completedMarkedKernel z, y.2 ∈ returnSet := by
  have he := returnLaw_ae_regeneration z
  rw [← completedMarked_forget z] at he
  exact (ae_map_iff measurable_snd.aemeasurable returnSet_measurable).mp he

lemma completedMarked_increment_law (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    (completedMarkedKernel (s,T)).map (markedShift (-T)) = sourceCycleLaw := by
  rw [completedMarked_regeneration s hs T]
  have ht := completedMarked_translation regenerationState 0 T
  simp only [zero_add] at ht
  rw [← ht,Measure.map_map (markedShift_measurable (-T)) (markedShift_measurable T)]
  have he : markedShift (-T) ∘ markedShift T = id := by
    funext z
    ext <;> simp [markedShift,shiftCost,Function.comp_apply,add_assoc]
  rw [he,Measure.map_id]
  rfl

def markCostProjection (z : MarkedOddCost) : Bool × ℝ := (z.1,z.2.2)

lemma markCostProjection_measurable : Measurable markCostProjection :=
  measurable_fst.prodMk (measurable_snd.comp measurable_snd)

noncomputable def jointMarkCostLaw : Measure (Bool × ℝ) := sourceCycleLaw.map markCostProjection

instance jointMarkCostLaw_isProbabilityMeasure : IsProbabilityMeasure jointMarkCostLaw := by
  unfold jointMarkCostLaw
  exact (Measure.isProbabilityMeasure_map_iff markCostProjection_measurable.aemeasurable).mpr inferInstance

lemma marked_cycle_increment_integral (z : OddCost) (hz : z ∈ returnSet)
    {F : Bool × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F (y.1,y.2.2-z.2) ∂completedMarkedKernel z) = ∫⁻ u, F u ∂jointMarkCostLaw := by
  have he := congrArg (fun μ : Measure MarkedOddCost => ∫⁻ y, F (markCostProjection y) ∂μ)
    (completedMarked_increment_law z.1 hz z.2)
  rw [lintegral_map (f := fun y : MarkedOddCost => F (markCostProjection y))
    (hF.comp markCostProjection_measurable) (markedShift_measurable (-z.2))] at he
  rw [jointMarkCostLaw,lintegral_map hF markCostProjection_measurable]
  simpa only [markCostProjection,markedShift,shiftCost,sub_eq_add_neg] using he

noncomputable def markedCycleProductExpectation : List (Bool × ℝ → ℝ≥0∞) → OddCost → ℝ≥0∞
  | [], _ => 1
  | F :: Fs, z => ∫⁻ y, F (y.1,y.2.2-z.2)*markedCycleProductExpectation Fs y.2 ∂completedMarkedKernel z

theorem finite_marked_cycle_factorization (Fs : List (Bool × ℝ → ℝ≥0∞))
    (hFs : ∀ F ∈ Fs, Measurable F) (z : OddCost) (hz : z ∈ returnSet) :
    markedCycleProductExpectation Fs z =
      (Fs.map (fun F => ∫⁻ u, F u ∂jointMarkCostLaw)).prod := by
  induction Fs generalizing z with
  | nil => rfl
  | cons F Fs ih =>
    have hF : Measurable F := hFs F (by simp)
    have hrest : ∀ G ∈ Fs, Measurable G := fun G hG => hFs G (by simp [hG])
    change (∫⁻ y, F (y.1,y.2.2-z.2)*markedCycleProductExpectation Fs y.2 ∂completedMarkedKernel z) =
      (∫⁻ u, F u ∂jointMarkCostLaw)*(Fs.map (fun F => ∫⁻ u, F u ∂jointMarkCostLaw)).prod
    calc
      _ = ∫⁻ y, F (y.1,y.2.2-z.2)*(Fs.map (fun F => ∫⁻ u, F u ∂jointMarkCostLaw)).prod ∂completedMarkedKernel z := by
        apply lintegral_congr_ae
        filter_upwards [completedMarked_ae_regeneration z] with y hy
        rw [ih hrest y.2 hy]
      _ = (∫⁻ y, F (y.1,y.2.2-z.2) ∂completedMarkedKernel z)*
          (Fs.map (fun F => ∫⁻ u, F u ∂jointMarkCostLaw)).prod :=
        lintegral_mul_const _ (hF.comp (measurable_fst.prodMk
          ((measurable_snd.comp measurable_snd).sub measurable_const)))
      _ = _ := by rw [marked_cycle_increment_integral z hz hF]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
