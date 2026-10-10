import OAI.Probability.FreeIsing.Posterior.ContinuousObservationHistory

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousNoiseSplit

open WienerSampler ContinuousObservationHistory

def futurePath (s : ℝ≥0) (f : Path) : Path :=
  ⟨fun t => f (s + t) - f s,
    (f.continuous.comp (continuous_const.add continuous_id)).sub continuous_const⟩

@[simp]
theorem futurePath_apply (s : ℝ≥0) (f : Path) (t : ℝ≥0) :
    futurePath s f t = f (s + t) - f s := rfl

theorem measurable_futurePath (s : ℝ≥0) : Measurable (futurePath s) := by
  apply measurable_path_of_eval
  intro t
  exact (continuous_eval_const (s + t)).measurable.sub (continuous_eval_const s).measurable

variable {ι : Type*}

def futureArray (s : ℝ≥0) (f : ι → Path) : ι → Path := fun i => futurePath s (f i)

theorem measurable_futureArray (s : ℝ≥0) : Measurable (futureArray (ι := ι) s) :=
  Measurable.of_eval fun i => (measurable_futurePath s).comp (measurable_pi_apply i)

theorem injective_split (s : ℝ≥0) : Function.Injective
    (fun f : ι → Path => (stoppedArray s f, futureArray s f)) := by
  intro f g h
  have hp := congrArg Prod.fst h
  have hf := congrArg Prod.snd h
  funext i
  apply ContinuousMap.ext
  intro t
  have hs : f i s = g i s := by
    have hh := congrArg (fun a : ι → Path => a i s) hp
    simpa only [stoppedArray, stoppedPath_apply, min_self] using hh
  by_cases hts : t ≤ s
  · have hh := congrArg (fun a : ι → Path => a i t) hp
    simpa only [stoppedArray, stoppedPath_apply, min_eq_left hts] using hh
  · have hst : s ≤ t := (lt_of_not_ge hts).le
    have hh := congrArg (fun a : ι → Path => a i (t - s)) hf
    simp only [futureArray, futurePath_apply, add_tsub_cancel_of_le hst, hs] at hh
    linarith

theorem measurableEmbedding_split [Countable ι] (s : ℝ≥0) : MeasurableEmbedding
    (fun f : ι → Path => (stoppedArray s f, futureArray s f)) :=
  ((measurable_stoppedArray s).prodMk (measurable_futureArray s)).measurableEmbedding
    (injective_split s)

theorem indepFun_future_conditionalCopies [Countable ι]
    {O X : Type*} [MeasurableSpace O] [MeasurableSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (s : ℝ≥0) (rho : Measure (ι → Path)) [IsProbabilityMeasure rho]
    (eta : Kernel (ι → Path) O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : (ι → Path) × O => (stoppedArray s q.1, past q.2))
      (fun q => futureArray s q.1) (rho ⊗ₘ eta)) :
    IndepFun (fun q : (ι → Path) × (O × O) =>
      (stoppedArray s q.1, (past q.2.1, past q.2.2)))
      (fun q => futureArray s q.1) (rho ⊗ₘ (eta ×ₖ eta)) :=
  KernelCompatibility.indepFun_future_conditionalCopies_of_reconstructible_split
    rho (stoppedArray s) (measurable_stoppedArray s)
    (futureArray s) (measurable_futureArray s) (measurableEmbedding_split s)
    eta past hpast hind

end Problem367.ContinuousNoiseSplit

end

end OAI
