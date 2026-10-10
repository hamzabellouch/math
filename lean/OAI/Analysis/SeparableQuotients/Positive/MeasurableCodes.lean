import OAI.Analysis.SeparableQuotients.Positive.RowEvaluation

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Sampling
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]


abbrev WeakUnitBall := {y : WeakDual ℝ E // ‖WeakDual.toStrongDual y‖ ≤ 1}

instance weakUnitBallCompact : CompactSpace (WeakUnitBall E) := by
  exact (isCompact_iff_compactSpace (s := {y : WeakDual ℝ E |
    ‖WeakDual.toStrongDual y‖ ≤ 1})).mp (by
      simpa only [Set.preimage, Metric.mem_closedBall, dist_zero_right] using
        (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) 1))

instance weakUnitBallMetrizable [SeparableSpace E] : MetrizableSpace (WeakUnitBall E) :=
  WeakDual.metrizable_of_isCompact ℝ E _ (isCompact_iff_compactSpace.mpr (weakUnitBallCompact E))

instance weakUnitBallSecondCountable [SeparableSpace E] :
    SecondCountableTopology (WeakUnitBall E) := by infer_instance

instance weakUnitBallMeasurable : MeasurableSpace (WeakUnitBall E) := borel _
instance weakUnitBallBorel : BorelSpace (WeakUnitBall E) := ⟨rfl⟩

lemma continuous_weakUnitBall_eval :
    Continuous (fun p : E × WeakUnitBall E => p.2.1 p.1) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hbound : ∀ q : E × WeakUnitBall E,
      ‖q.2.1 (q.1 - p.1)‖ ≤ ‖q.1 - p.1‖ := by
    intro q
    exact (WeakDual.toStrongDual q.2.1).le_opNorm (q.1 - p.1) |>.trans
      ((mul_le_mul_of_nonneg_right q.2.2 (norm_nonneg _)).trans_eq (one_mul _))
  have hdiff : Tendsto (fun q : E × WeakUnitBall E => q.2.1 (q.1 - p.1))
      (𝓝 p) (𝓝 0) := by
    apply squeeze_zero_norm hbound
    have hh : Continuous (fun q : E × WeakUnitBall E => ‖q.1 - p.1‖) :=
      (continuous_fst.sub continuous_const).norm
    simpa only [sub_self, norm_zero] using hh.tendsto p
  have hfix : Continuous (fun q : E × WeakUnitBall E => q.2.1 p.1) :=
    (WeakDual.eval_continuous p.1).comp (continuous_subtype_val.comp continuous_snd)
  have hh := hdiff.add hfix.continuousAt
  simpa only [ContinuousAt, map_sub, sub_add_cancel, zero_add] using hh

variable [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]

omit [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_sequence_eval (n : ℕ) :
    Continuous (fun p : (ℕ → E) × WeakUnitBall E => p.2.1 (p.1 n)) :=
  (continuous_weakUnitBall_eval E).comp (f := fun p : (ℕ → E) × WeakUnitBall E => (p.1 n, p.2))
    (((continuous_apply n).comp continuous_fst).prodMk continuous_snd)

lemma measurable_sequence_eval (n : ℕ) :
    Measurable (fun p : (ℕ → E) × WeakUnitBall E => p.2.1 (p.1 n)) :=
  (continuous_sequence_eval E n).measurable

def limitOrZero {A : Type*} (f : ℕ → A → ℝ) (a : A) : ℝ :=
  if ∃ r, Tendsto (fun n => f n a) atTop (𝓝 r) then
    limUnder atTop (fun n => f n a) else 0

lemma limitOrZero_of_tendsto {A : Type*} {f : ℕ → A → ℝ} {a : A} {r : ℝ}
    (h : Tendsto (fun n => f n a) atTop (𝓝 r)) : limitOrZero f a = r := by
  have hc : ∃ r, Tendsto (fun n => f n a) atTop (𝓝 r) := ⟨r, h⟩
  simp only [limitOrZero, ite_eq_left hc, h.limUnder_eq]

lemma limitOrZero_of_not_tendsto {A : Type*} {f : ℕ → A → ℝ} {a : A}
    (h : ¬ ∃ r, Tendsto (fun n => f n a) atTop (𝓝 r)) :
    limitOrZero f a = 0 := by
  simp only [limitOrZero, ite_eq_right h]

lemma measurable_limitOrZero {A : Type*} [MeasurableSpace A]
    {f : ℕ → A → ℝ} (hf : ∀ n, Measurable (f n)) : Measurable (limitOrZero f) := by
  unfold limitOrZero
  apply Measurable.ite (measurableSet_exists_tendsto (l := atTop) hf)
  · exact (StronglyMeasurable.limUnder (fun n => (hf n).stronglyMeasurable)).measurable
  · exact measurable_const


end SeparableQuotient.Positive.Sampling

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Sampling
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]



local instance dualSubmoduleNormedGroup (F : Submodule ℝ (StrongDual ℝ X)) :
    NormedAddCommGroup F := Submodule.normedAddCommGroup F
local instance dualSubmoduleNormedSpace (F : Submodule ℝ (StrongDual ℝ X)) :
    NormedSpace ℝ F := Submodule.normedSpace F


def evaluation (F : Submodule ℝ (StrongDual ℝ X)) : X →L[ℝ] StrongDual ℝ F :=
  F.subtypeL.flip

@[simp] lemma evaluation_apply (F : Submodule ℝ (StrongDual ℝ X)) (x : X) (f : F) :
    evaluation F x f = f.val x := rfl

lemma norm_evaluation_le (F : Submodule ℝ (StrongDual ℝ X)) : ‖evaluation F‖ ≤ 1 := by
  rw [evaluation, ContinuousLinearMap.opNorm_flip]
  exact Submodule.norm_subtypeL_le F


def evaluationBall (F : Submodule ℝ (StrongDual ℝ X)) (x : {x : X // ‖x‖ ≤ 1}) :
    WeakUnitBall F :=
  ⟨StrongDual.toWeakDual (evaluation F x.val),
    (evaluation F).le_opNorm x.val |>.trans
      ((mul_le_mul_of_nonneg_right (norm_evaluation_le F) (norm_nonneg _)).trans
        (by simpa using x.property))⟩

variable (F : Submodule ℝ (StrongDual ℝ X)) [SeparableSpace F]


def sequentialCodeValue : (ℕ → F) × WeakUnitBall F → ℝ :=
  limitOrZero (fun n p => p.2.val (p.1 n))

lemma measurable_sequentialCodeValue :
    letI : MeasurableSpace F := borel F
    Measurable (sequentialCodeValue F) := by
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  exact measurable_limitOrZero (measurable_sequence_eval F)

omit [SeparableSpace F] in
lemma sequentialCodeValue_eq {c : ℕ → F} {h : StrongDual ℝ (StrongDual ℝ F)}
    (hc : ∀ y : StrongDual ℝ F, Tendsto (fun n => y (c n)) atTop (𝓝 (h y)))
    (y : WeakUnitBall F) : sequentialCodeValue F (c, y) = h (WeakDual.toStrongDual y.val) :=
  limitOrZero_of_tendsto (hc _)

omit [SeparableSpace F] in
lemma sequentialCodeValue_evaluation {c : ℕ → F} {h : StrongDual ℝ (StrongDual ℝ F)}
    (hc : ∀ y : StrongDual ℝ F, Tendsto (fun n => y (c n)) atTop (𝓝 (h y)))
    (x : {x : X // ‖x‖ ≤ 1}) :
    sequentialCodeValue F (c, evaluationBall F x) = (h.comp (evaluation F)) x.val := by
  exact sequentialCodeValue_eq F hc _

end SeparableQuotient.Positive.Sampling

end

end

end OAI
