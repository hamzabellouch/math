import OAI.NumberTheory.Jacobsthal.Estimates.RawInitialEven

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.InitialOddDraw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.TransitionKernels

lemma initialOddReturnJoint_endpoint (s : EvenState) :
    (initialOddReturnJoint s).map Prod.snd=delayedRegeneration s := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF measurable_snd,initialOddReturnJoint,
    Kernel.lintegral_compProd _ _ _ (f := fun p : OddCost × OddCost => F p.2) (hF.comp measurable_snd),
    delayedRegeneration,Kernel.lintegral_comp _ _ _ hF]
  rfl

noncomputable def rawInitialEndpointState (a : ℕ) (r : RawInitialEvenTrace a) : CostState :=
  (rawContinuationSignature (a+1) r).2

lemma rawInitialEndpointState_measurable (a : ℕ) : Measurable (rawInitialEndpointState a) :=
  measurable_snd.comp (rawContinuationSignature_measurable (a+1))

lemma rawInitialEven_endpoint (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) :
    (rawInitialEvenKernel a h).map (rawInitialEndpointState a)=(delayedRegeneration s).map embedOdd := by
  have he := congrArg (fun μ : Measure (CostState × CostState) => μ.map Prod.snd)
    (rawInitialEven_joint_signature a h s hs)
  rw [Measure.map_map measurable_snd (rawContinuationSignature_measurable _),
    Measure.map_map measurable_snd embedOddPair_measurable] at he
  rw [← initialOddReturnJoint_endpoint s,
    Measure.map_map embedOdd_measurable measurable_snd]
  exact he

noncomputable def rawInitialEvenCostLaw (a : ℕ) (h : RawHistory a) : Measure ℝ :=
  (rawInitialEvenKernel a h).map (fun r => (rawInitialEndpointState a r).2)

theorem rawInitialEven_cost_law (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) : rawInitialEvenCostLaw a h=delayedCostLaw s := by
  calc
    _ = ((rawInitialEvenKernel a h).map (rawInitialEndpointState a)).map Prod.snd :=
      (Measure.map_map measurable_snd (rawInitialEndpointState_measurable a)).symm
    _ = ((delayedRegeneration s).map embedOdd).map Prod.snd := by rw [rawInitialEven_endpoint a h s hs]
    _ = _ := by
      rw [Measure.map_map measurable_snd embedOdd_measurable]
      rfl

theorem rawInitialEven_endpoint_regenerates (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) :
    ∀ᵐ r ∂rawInitialEvenKernel a h, rawInitialEndpointState a r ∈ regenerationSet := by
  apply (ae_map_iff (rawInitialEndpointState_measurable a).aemeasurable regenerationSet_measurable).mp
  rw [rawInitialEven_endpoint a h s hs]
  apply (ae_map_iff embedOdd_measurable.aemeasurable regenerationSet_measurable).mpr
  exact delayedRegeneration_ae_regeneration s

theorem rawInitialEven_uniform_exponential (S : ℝ) : ∃ eta B : ℝ, 0 < eta ∧ 0 ≤ B ∧
    ∀ (a : ℕ) (h : RawHistory a) (s : EvenState), rawLast a h=(Sum.inl s,0) → s.1 ≤ S →
      costTransform (rawInitialEvenCostLaw a h) eta ≤ ENNReal.ofReal B := by
  obtain ⟨eta,B,heta,hB,hMoment⟩ := delayedCostLaw_uniform_exponential S
  refine ⟨eta,B,heta,hB,?_⟩
  intro a h s hs hS
  rw [rawInitialEven_cost_law a h s hs]
  exact hMoment s hS

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
