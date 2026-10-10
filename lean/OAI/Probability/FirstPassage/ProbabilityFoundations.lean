import OAI.Probability.FirstPassage.PassageTime
import Mathlib.Probability.Independence.InfinitePi

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Filter

instance : Countable Step := by
  let code : Step → ℕ := fun d => match d with
    | .east => 0 | .west => 1 | .north => 2 | .south => 3
  have hi : Function.Injective code := by
    intro d e h
    cases d <;> cases e <;> simp_all [code]
  exact hi.countable

noncomputable instance rateOneProbability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

noncomputable def exponentialProductLaw : Measure (Edge → ℝ) :=
  Measure.infinitePi (fun _ : Edge => expMeasure 1)

theorem exponentialProductLaw_environment :
    ExponentialEnvironment exponentialProductLaw (fun e ω => ω e) where
  probability := inferInstanceAs
    (IsProbabilityMeasure (Measure.infinitePi (fun _ : Edge => expMeasure 1)))
  measurable := measurable_pi_apply
  independent := iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  marginal := Measure.infinitePi_map_eval _

theorem rateOne_ae_positive : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  have hc : (expMeasure 1 (Iic 0)).toReal = 0 := by
    rw [← measureReal_def, ← cdf_eq_real]
    simp [cdf_expMeasure_eq (r := 1) (by norm_num)]
  have hz : expMeasure 1 (Iic 0) = 0 :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.zero_ne_top).mp
      (by simpa using hc)
  simpa only [ae_iff, not_lt, Iic] using hz

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.ae_positive (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ e, 0 < τ e ω := by
  rw [ae_all_iff]
  intro e
  have hp : ∀ᵐ x ∂Measure.map (τ e) P, 0 < x := by
    rw [h.marginal e]
    exact rateOne_ae_positive
  exact (ae_map_iff (h.measurable e).aemeasurable measurableSet_Ioi).mp hp

theorem measurable_pathCost (hτ : ∀ e, Measurable (τ e))
    (p : Vertex) (ds : List Step) :
    Measurable (fun ω => pathCost (fun e => τ e ω) p ds) := by
  induction ds generalizing p with
  | nil => exact measurable_const
  | cons d ds ih => exact (hτ _).add (ih _)

theorem measurable_passageTime (hτ : ∀ e, Measurable (τ e)) (p q : Vertex) :
    Measurable (fun ω => passageTime (fun e => τ e ω) p q) := by
  have hm := Measurable.sInf (Set.to_countable {ds : List Step |
    p + displacement ds = q}) (fun ds _ => measurable_pathCost hτ p ds)
  convert hm using 1
  funext ω
  unfold passageTime
  congr 1

theorem measurableSet_strict_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds < bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_lt (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

theorem measurableSet_bounded_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds ≤ bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_le (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

end PlanarFPP

end OAI
