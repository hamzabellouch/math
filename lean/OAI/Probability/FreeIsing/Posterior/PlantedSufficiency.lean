import OAI.Probability.FreeIsing.Estimates.TerminalSufficiency
import OAI.Probability.FreeIsing.Posterior.PlantedBridge

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal

namespace Problem367.TerminalSufficiency

theorem condExp_planted_past_eq_terminal
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : Measure Ω) [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t))
    (signal f : S → ℝ) (hSignal : Measurable signal) (hf : Measurable f)
    (hfint : Integrable f ν) {T : ℝ≥0} (hT : T ≠ 0) :
    (ν.prod μ)[(fun q : S × Ω => f q.1) |
      MeasurableSpace.comap
        (fun q : S × Ω => fun s : Set.Iic T =>
          (s.1 : ℝ) * signal q.1 + B s.1 q.2) inferInstance] =ᵐ[ν.prod μ]
    (ν.prod μ)[(fun q : S × Ω => f q.1) |
      MeasurableSpace.comap
        (fun q : S × Ω => (T : ℝ) * signal q.1 + B T q.2) inferInstance] := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let Y : S × Ω → ℝ := fun q => (T : ℝ) * signal q.1 + B T q.2
  let X : S × Ω → Set.Iic T → ℝ :=
    fun q s => (s.1 : ℝ) * signal q.1 + B s.1 q.2
  let R : S × Ω → Set.Iic T → ℝ :=
    fun q s => brownianBridge B T s q.2
  have hBridge : Measurable (fun w (s : Set.Iic T) => brownianBridge B T s w) := by
    apply Measurable.of_eval
    intro s
    exact (hmB s).sub ((hmB T).const_mul _)
  have hYm : Measurable Y := by
    exact ((hSignal.comp measurable_fst).const_mul (T : ℝ)).add
      ((hmB T).comp measurable_snd)
  have hRm : Measurable R := hBridge.comp measurable_snd
  have hInd : IndepFun (fun q : S × Ω => (f q.1, Y q)) R (ν.prod μ) := by
    have hi := Problem367.indepFun_prod_left_of_indepFun ν μ (hmB T) hBridge
      (Problem367.preBrownian_bridge_indep_terminal hB hT).symm
    have hm : Measurable (fun q : S × ℝ => (f q.1, (T : ℝ) * signal q.1 + q.2)) := by
      fun_prop
    simpa only [Function.comp_def, id_eq] using hi.comp hm measurable_id
  apply condExp_path_eq_terminal_of_indep_residual (ν.prod μ)
    (fun q => f q.1) Y X R (fun s : Set.Iic T => (s.1 : ℝ) / (T : ℝ))
    (⟨T, by simp⟩ : Set.Iic T) (hf.comp measurable_fst) hYm hRm
    (hfint.comp_fst μ) hInd
  · intro q s
    have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    dsimp [X, Y, R, brownianBridge]
    field_simp
    ring
  · intro q
    rfl

end Problem367.TerminalSufficiency

end

end OAI
