import OAI.Probability.SpanningForest.GlobalWiener
import OAI.Probability.SpanningForest.BrownianReference
import OAI.Probability.SpanningForest.BrownianCanonicalPosterior

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336.CanonicalBrownianReference

local instance : MeasurableSpace GlobalWiener.Path := borel _
local instance : BorelSpace GlobalWiener.Path := ⟨rfl⟩

abbrev Space (I : Type*) := (I → Bool) × (I → GlobalWiener.Path)

def noiseLaw (I : Type*) : Measure (I → GlobalWiener.Path) :=
  Measure.infinitePi (fun _ : I => GlobalWiener.wienerMeasure)

instance noiseLaw_probability (I : Type*) : IsProbabilityMeasure (noiseLaw I) := by
  unfold noiseLaw
  infer_instance

def law {I : Type*} (μ : ProbabilityMeasure (I → Bool)) : Measure (Space I) :=
  BrownianReference.coupling (μ : Measure (I → Bool)) GlobalWiener.wienerMeasure

instance law_probability {I : Type*} (μ : ProbabilityMeasure (I → Bool)) :
    IsProbabilityMeasure (law μ) := by
  unfold law
  infer_instance

def hidden {I : Type*} (q : Space I) : I → Bool := q.1

def noise {I : Type*} (i : I) (t : ℝ≥0) (q : Space I) : ℝ := q.2 i t

def observation {I : Type*} (t : ℝ≥0) (q : Space I) (i : I) : ℝ :=
  (t : ℝ) * TiltLimit.bit (hidden q i) + noise i t q

variable {I : Type*} (μ : ProbabilityMeasure (I → Bool))

theorem hidden_measurable : Measurable (hidden (I := I)) := measurable_fst

theorem hidden_hasLaw : HasLaw hidden (μ : Measure (I → Bool)) (law μ) :=
  BrownianReference.hidden_hasLaw (μ : Measure (I → Bool)) GlobalWiener.wienerMeasure

theorem paths_hasLaw :
    HasLaw (fun q : Space I => q.2) (noiseLaw I) (law μ) :=
  measurePreserving_snd.hasLaw

theorem raw_noise_hasLaw :
    HasLaw (fun (q : Space I) i t => noise i t q)
      ((noiseLaw I).map (fun (w : I → GlobalWiener.Path) i t => w i t)) (law μ) := by
  have hm : Measurable (fun (w : I → GlobalWiener.Path) i t => w i t) :=
    Measurable.of_eval (fun i => Measurable.of_eval (fun t =>
      (continuous_eval_const t).measurable.comp (measurable_pi_apply i)))
  exact (show HasLaw (fun (w : I → GlobalWiener.Path) i t => w i t)
    ((noiseLaw I).map (fun (w : I → GlobalWiener.Path) i t => w i t))
    (noiseLaw I) from ⟨hm.aemeasurable, rfl⟩).comp (paths_hasLaw μ)

theorem noise_measurable (i : I) (t : ℝ≥0) : Measurable (noise i t) :=
  (continuous_eval_const t).measurable.comp ((measurable_pi_apply i).comp measurable_snd)

theorem noise_jointlyMeasurable (i : I) :
    Measurable (fun p : ℝ≥0 × Space I => noise i p.1 p.2) := by
  exact continuous_eval.measurable.comp
    (((measurable_pi_apply i).comp measurable_snd.snd).prodMk measurable_fst)

theorem noise_continuous (q : Space I) (i : I) :
    Continuous (fun t => noise i t q) := (q.2 i).continuous

theorem noise_brownian (i : I) : IsBrownianReal (noise i) (law μ) :=
  BrownianReference.brownian_process (μ : Measure (I → Bool))
    GlobalWiener.wienerMeasure GlobalWiener.isBrownian_wienerMeasure i

theorem noise_independent :
    iIndepFun (fun i (q : Space I) t => noise i t q) (law μ) :=
  BrownianReference.independent_processes (μ : Measure (I → Bool))
    GlobalWiener.wienerMeasure (fun t w => w t)
    (fun t => (continuous_eval_const t).measurable)

theorem hidden_independent_flat_noise :
    IndepFun hidden (fun (q : Space I) (p : I × ℝ≥0) => noise p.1 p.2 q) (law μ) :=
  BrownianReference.hidden_independent_field (μ : Measure (I → Bool))
    GlobalWiener.wienerMeasure (fun t w => w t)
    (fun t => (continuous_eval_const t).measurable)

theorem hidden_independent_noise :
    IndepFun hidden (fun (q : Space I) i t => noise i t q) (law μ) := by
  exact (hidden_independent_flat_noise μ).comp measurable_id
    (show Measurable (fun f : I × ℝ≥0 → ℝ => fun i t => f (i, t)) by fun_prop)

theorem bit_hidden_measurable :
    Measurable (fun q : Space I => fun i => TiltLimit.bit (hidden q i)) := by
  apply Measurable.of_eval
  intro i
  exact TiltLimit.continuous_bit.measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)

theorem bit_hidden_independent_noise :
    IndepFun (fun q : Space I => fun i => TiltLimit.bit (hidden q i))
      (fun (q : Space I) i t => noise i t q) (law μ) := by
  exact (hidden_independent_noise μ).comp
    (Measurable.of_eval (fun i => TiltLimit.continuous_bit.measurable.comp
      (measurable_pi_apply i))) measurable_id

theorem bit_hidden_mem_Icc (q : Space I) (i : I) :
    TiltLimit.bit (hidden q i) ∈ Set.Icc (0 : ℝ) 1 := by
  cases hidden q i <;> norm_num [TiltLimit.bit]

theorem observation_continuous (q : Space I) (i : I) :
    Continuous (fun t => observation t q i) :=
  (continuous_subtype_val.mul continuous_const).add (noise_continuous q i)

theorem observation_jointlyMeasurable :
    Measurable (fun p : ℝ≥0 × Space I => observation p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_subtype_coe.comp measurable_fst).mul
    (TiltLimit.continuous_bit.measurable.comp
      ((measurable_pi_apply i).comp measurable_snd.fst))).add (noise_jointlyMeasurable i)

theorem posterior [Countable I]
    (S : I → ℕ → Finset I) (e : I)
    (hS : Monotone (S e)) (hcover : ∀ i, ∃ n, i ∈ S e n) (t : ℝ≥0) :
    (fun q : Space I => PosteriorDrift.drift μ S t (observation t q) e) =ᵐ[law μ]
      (law μ)[fun q => TiltLimit.bit (hidden q e) |
        Observation.historySigma (fun i (s : Set.Iic t) q => observation s q i)] := by
  exact Observation.drift_eq_condExp_brownian_history_all_times
    (law μ) μ hidden hidden_measurable (hidden_hasLaw μ).map_eq noise
    (fun i => (noise_brownian μ i).toIsPreBrownianReal) (noise_independent μ)
    noise_measurable (hidden_independent_flat_noise μ) S e hS hcover t

end Problem336.CanonicalBrownianReference

end

end OAI
