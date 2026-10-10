import OAI.NumberTheory.Jacobsthal.Analysis.DensityConservation

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.OrdinaryKernelInvariance
open NumberTheoryLean NumberTheoryLean.DerivativeWeights NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels NumberTheoryLean.KernelDensityBridge
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.IncomingDensityIdentities Erdos970Dependency.DensityConservation

noncomputable def evenLift (s : ℝ) : EvenState := ⟨max (198 / 100) s, le_max_left _ _⟩
noncomputable def oddLift (s : ℝ) : OddState := ⟨max (95 / 100) s, le_max_left _ _⟩

theorem evenLift_measurable : Measurable evenLift :=
  (measurable_const.max measurable_id).subtype_mk

theorem oddLift_measurable : Measurable oddLift :=
  (measurable_const.max measurable_id).subtype_mk

noncomputable def evenRealKernel : Kernel ℝ ℝ := evenKernel.comap evenLift evenLift_measurable
noncomputable def oddRealKernel : Kernel ℝ ℝ := oddKernel.comap oddLift oddLift_measurable

instance evenRealKernel_isMarkovKernel : IsMarkovKernel evenRealKernel := by unfold evenRealKernel; infer_instance
instance oddRealKernel_isMarkovKernel : IsMarkovKernel oddRealKernel := by unfold oddRealKernel; infer_instance

theorem even_lifted_product (s t : ℝ) :
    InvariantDensities.evenDensity s * transitionDensity .even (evenLift s).1 t = incomingEven t s := by
  by_cases hs : 2 ≤ s
  · have heq : (evenLift s).1 = s := max_eq_right (by linarith)
    rw [heq]
    rfl
  · rw [incomingEven, InvariantDensities.evenDensity,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul, zero_mul]

theorem odd_lifted_product (s t : ℝ) :
    InvariantDensities.oddDensity s * transitionDensity .odd (oddLift s).1 t = incomingOdd t s := by
  by_cases hs : 1 ≤ s
  · have heq : (oddLift s).1 = s := max_eq_right (by linarith)
    rw [heq]
    rfl
  · rw [incomingOdd, InvariantDensities.oddDensity,
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul, zero_mul]

theorem even_ratio_invariance : evenRealKernel ∘ₘ evenMeasure = oddMeasure := by
  apply kernel_density_conservation evenRealKernel InvariantDensities.evenDensity
    InvariantDensities.oddDensity (fun s t ↦ transitionDensity .even (evenLift s).1 t)
    InvariantDensities.evenDensity_measurable InvariantDensities.evenDensity_nonneg
  · exact (InvariantDensities.evenDensity_measurable.comp measurable_fst).mul
      ((transitionDensity_joint_measurable .even).comp
        (((measurable_subtype_coe.comp evenLift_measurable).comp measurable_fst).prodMk measurable_snd))
  · intro s B _
    exact evenKernel_apply (evenLift s) B
  · intro t
    rw [show (fun s ↦ InvariantDensities.evenDensity s * transitionDensity .even (evenLift s).1 t) =
      incomingEven t from funext (fun s ↦ even_lifted_product s t)]
    exact incomingEven_integrable t
  · intro s t
    exact mul_nonneg (InvariantDensities.evenDensity_nonneg s)
      (TransitionKernels.evenDensity_nonneg (evenLift s) t)
  · intro t
    simp_rw [even_lifted_product]
    exact incomingEven_integral t

theorem odd_ratio_invariance : oddRealKernel ∘ₘ oddMeasure = evenMeasure := by
  apply kernel_density_conservation oddRealKernel InvariantDensities.oddDensity
    InvariantDensities.evenDensity (fun s t ↦ transitionDensity .odd (oddLift s).1 t)
    InvariantDensities.oddDensity_measurable InvariantDensities.oddDensity_nonneg
  · exact (InvariantDensities.oddDensity_measurable.comp measurable_fst).mul
      ((transitionDensity_joint_measurable .odd).comp
        (((measurable_subtype_coe.comp oddLift_measurable).comp measurable_fst).prodMk measurable_snd))
  · intro s B _
    exact oddKernel_apply (oddLift s) B
  · intro t
    rw [show (fun s ↦ InvariantDensities.oddDensity s * transitionDensity .odd (oddLift s).1 t) =
      incomingOdd t from funext (fun s ↦ odd_lifted_product s t)]
    exact incomingOdd_integrable t
  · intro s t
    exact mul_nonneg (InvariantDensities.oddDensity_nonneg s)
      (TransitionKernels.oddDensity_nonneg (oddLift s) t)
  · intro t
    simp_rw [odd_lifted_product]
    exact incomingOdd_integral t

end Erdos970Dependency.OrdinaryKernelInvariance

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.StateKernelInvariance
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures NumberTheoryLean.KernelDensityBridge
open Erdos970Dependency.InvariantFiniteness Erdos970Dependency.OrdinaryKernelInvariance

theorem comp_map_input {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (K : Kernel β γ) (mu : Measure α) (f : α → β) (hf : Measurable f) :
    K ∘ₘ mu.map f = K.comap f hf ∘ₘ mu := by
  ext B hB
  rw [Measure.bind_apply hB K.aemeasurable, lintegral_map (K.measurable_coe hB) hf,
    Measure.bind_apply hB (K.comap f hf).aemeasurable]
  rfl

theorem oddLift_ratio (s : OddState) : oddLift s.1 = s := by
  apply Subtype.ext
  exact max_eq_right s.2

theorem evenLift_ratio (s : EvenState) : evenLift s.1 = s := by
  apply Subtype.ext
  exact max_eq_right s.2

theorem evenKernel_map_lift (s : EvenState) : (evenKernel s).map oddLift = evenToOdd s := by
  rw [← evenToOdd_map_ratio s, Measure.map_map oddLift_measurable measurable_subtype_coe]
  rw [show oddLift ∘ (Subtype.val : OddState → ℝ) = id from funext oddLift_ratio, Measure.map_id]

theorem oddKernel_map_lift (s : OddState) : (oddKernel s).map evenLift = oddToEven s := by
  rw [← oddToEven_map_ratio s, Measure.map_map evenLift_measurable measurable_subtype_coe]
  rw [show evenLift ∘ (Subtype.val : EvenState → ℝ) = id from funext evenLift_ratio, Measure.map_id]

noncomputable def evenStateMeasure : Measure EvenState := evenMeasure.map evenLift
noncomputable def oddStateMeasure : Measure OddState := oddMeasure.map oddLift

instance evenStateMeasure_isFiniteMeasure : IsFiniteMeasure evenStateMeasure := by unfold evenStateMeasure; infer_instance
instance oddStateMeasure_isFiniteMeasure : IsFiniteMeasure oddStateMeasure := by unfold oddStateMeasure; infer_instance

theorem even_state_invariance : evenToOdd ∘ₘ evenStateMeasure = oddStateMeasure := by
  have h := congrArg (fun mu : Measure ℝ ↦ mu.map oddLift) even_ratio_invariance
  rw [Measure.map_comp _ _ oddLift_measurable] at h
  have hK : evenRealKernel.map oddLift = evenToOdd.comap evenLift evenLift_measurable := by
    ext s B hB
    rw [Kernel.map_apply _ oddLift_measurable]
    change (evenKernel (evenLift s)).map oddLift B = evenToOdd (evenLift s) B
    rw [evenKernel_map_lift]
  rw [hK, ← comp_map_input] at h
  exact h

theorem odd_state_invariance : oddToEven ∘ₘ oddStateMeasure = evenStateMeasure := by
  have h := congrArg (fun mu : Measure ℝ ↦ mu.map evenLift) odd_ratio_invariance
  rw [Measure.map_comp _ _ evenLift_measurable] at h
  have hK : oddRealKernel.map evenLift = oddToEven.comap oddLift oddLift_measurable := by
    ext s B hB
    rw [Kernel.map_apply _ evenLift_measurable]
    change (oddKernel (oddLift s)).map evenLift B = oddToEven (oddLift s) B
    rw [oddKernel_map_lift]
  rw [hK, ← comp_map_input] at h
  exact h

noncomputable def stateMeasure : Measure State :=
  evenStateMeasure.map Sum.inl + oddStateMeasure.map Sum.inr

instance stateMeasure_isFiniteMeasure : IsFiniteMeasure stateMeasure := by unfold stateMeasure; infer_instance

theorem state_invariance : stateKernel ∘ₘ stateMeasure = stateMeasure := by
  have he : stateKernel ∘ₘ evenStateMeasure.map Sum.inl = oddStateMeasure.map Sum.inr := by
    rw [comp_map_input _ _ _ measurable_inl]
    change evenBranch ∘ₘ evenStateMeasure = _
    rw [evenBranch, ← Measure.map_comp _ _ measurable_inr, even_state_invariance]
  have ho : stateKernel ∘ₘ oddStateMeasure.map Sum.inr = evenStateMeasure.map Sum.inl := by
    rw [comp_map_input _ _ _ measurable_inr]
    change oddBranch ∘ₘ oddStateMeasure = _
    rw [oddBranch, ← Measure.map_comp _ _ measurable_inl, odd_state_invariance]
  rw [stateMeasure, Measure.comp_add, he, ho, add_comm]

end Erdos970Dependency.StateKernelInvariance

end

end Erdos970

end OAI
