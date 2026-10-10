import OAI.Probability.FreeIsing.Conditioning.CopyFiltration
import OAI.Probability.FreeIsing.Stochastic.WienerSampler

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousObservationHistory

open WienerSampler

def stoppedPath (s : ℝ≥0) (f : Path) : Path :=
  ⟨fun t => f (min t s), f.continuous.comp (continuous_id.min continuous_const)⟩

@[simp]
theorem stoppedPath_apply (s : ℝ≥0) (f : Path) (t : ℝ≥0) :
    stoppedPath s f t = f (min t s) := rfl

theorem measurable_stoppedPath (s : ℝ≥0) : Measurable (stoppedPath s) := by
  apply measurable_path_of_eval
  intro t
  exact (continuous_eval_const (min t s)).measurable

theorem stoppedPath_stoppedPath {s t : ℝ≥0} (hst : s ≤ t) (f : Path) :
    stoppedPath s (stoppedPath t f) = stoppedPath s f := by
  ext u
  simp only [stoppedPath_apply, min_eq_left ((min_le_right u s).trans hst)]

variable {ι : Type*}

def stoppedArray (s : ℝ≥0) (f : ι → Path) : ι → Path :=
  fun i => stoppedPath s (f i)

theorem measurable_stoppedArray (s : ℝ≥0) : Measurable (stoppedArray (ι := ι) s) := by
  exact Measurable.of_eval fun index =>
    (measurable_stoppedPath s).comp (measurable_pi_apply index)

theorem stoppedArray_stoppedArray {s t : ℝ≥0} (hst : s ≤ t) (f : ι → Path) :
    stoppedArray s (stoppedArray t f) = stoppedArray s f := by
  funext i
  exact stoppedPath_stoppedPath hst (f i)

theorem monotone_stoppedArray_comap : Monotone
    (fun s => MeasurableSpace.comap (stoppedArray (ι := ι) s) inferInstance) := by
  intro s t hst
  have h := MeasurableSpace.comap_mono (g := stoppedArray (ι := ι) t)
    (measurable_stoppedArray (ι := ι) s).comap_le
  simpa only [MeasurableSpace.comap_comp, Function.comp_def,
    stoppedArray_stoppedArray hst] using h

theorem measurable_stoppedArray_of_eval {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (s : ℝ≥0) (F : Ω → ι → Path)
    (hF : ∀ i t, t ≤ s → Measurable (fun ω => F ω i t)) :
    Measurable (fun ω => stoppedArray s (F ω)) := by
  apply Measurable.of_eval
  intro i
  apply measurable_path_of_eval
  intro t
  exact hF i (min t s) (min_le_right t s)

theorem measurable_past_of_stoppedArray {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (s : ℝ≥0) (F : Ω → ι → Path)
    (hF : Measurable (fun ω => stoppedArray s (F ω))) :
    Measurable (fun ω i (t : Set.Iic s) => F ω i t) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro t
  have h := (continuous_eval_const (t : ℝ≥0)).measurable.comp
    ((measurable_pi_apply i).comp hF)
  simpa only [Function.comp_def, stoppedArray, stoppedPath_apply,
    min_eq_left (show (t : ℝ≥0) ≤ s from t.property)] using h

theorem stoppedArray_comap_eq_past (s : ℝ≥0) :
    MeasurableSpace.comap (stoppedArray (ι := ι) s) inferInstance =
      MeasurableSpace.comap
        (fun f : ι → Path => fun i (t : Set.Iic s) => f i t) inferInstance := by
  apply le_antisymm
  · let m := MeasurableSpace.comap
      (fun f : ι → Path => fun i (t : Set.Iic s) => f i t) inferInstance
    have hp : @Measurable (ι → Path) (ι → Set.Iic s → ℝ) m inferInstance
        (fun f i t => f i t) := comap_measurable _
    have hs := measurable_stoppedArray_of_eval (mΩ := m) s (fun f : ι → Path => f)
      (fun i t ht => (measurable_pi_apply (⟨t, ht⟩ : Set.Iic s)).comp
        ((measurable_pi_apply i).comp hp))
    exact hs.comap_le
  · exact (measurable_past_of_stoppedArray
      (mΩ := MeasurableSpace.comap (stoppedArray (ι := ι) s) inferInstance)
      s (fun f : ι → Path => f) (comap_measurable _)).comap_le

theorem stoppedArray_comap_eq_natural (s : ℝ≥0) :
    MeasurableSpace.comap (stoppedArray (ι := ι) s) inferInstance =
      ⨆ i : ι, Filtration.natural (fun t (f : ι → Path) => f i t)
        (fun t => ((continuous_eval_const t).measurable.comp
          (measurable_pi_apply i)).stronglyMeasurable) s := by
  rw [stoppedArray_comap_eq_past]
  simp only [MeasurableSpace.comap_process_pi, Filtration.natural_eq_comap]

def joinedFiltration : Filtration ℝ≥0
    (inferInstance : MeasurableSpace ((ℝ≥0 → ι → ℝ) × ((ι → Path) × (ι → Path)))) :=
  ConditionalCopyBrownian.joinedFiltration stoppedArray measurable_stoppedArray
    monotone_stoppedArray_comap

theorem commonNoise_martingale [Countable ι]
    (i : ι) (rho : Measure (ℝ≥0 → ι → ℝ)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ℝ≥0 → ι → ℝ) => w t i) rho)
    (eta : Kernel (ℝ≥0 → ι → ℝ) (ι → Path)) [IsMarkovKernel eta]
    (hind : ∀ s, IndepFun
      (fun q : (ℝ≥0 → ι → ℝ) × (ι → Path) =>
        (PathSplit.pastPath s q.1, stoppedArray s q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta)) :
    Martingale (fun t (q : (ℝ≥0 → ι → ℝ) × ((ι → Path) × (ι → Path))) => q.1 t i)
      joinedFiltration (rho ⊗ₘ (eta ×ₖ eta)) :=
  ConditionalCopyArrayBrownian.commonNoise_martingale_joinedFiltration i rho hB eta
    stoppedArray measurable_stoppedArray monotone_stoppedArray_comap hind

end Problem367.ContinuousObservationHistory

end

end OAI
