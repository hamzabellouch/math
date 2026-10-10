import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem336AdditiveD139

def continuousPathInput {I : Type u_1} (w : I → C(ℝ≥0, ℝ))
    (t : ℝ) (i : I) : ℝ := w i (Real.toNNReal t)

theorem continuous_continuousPathInput {I : Type u_2}
    (w : I → C(ℝ≥0, ℝ)) (i : I) :
    Continuous (fun t => continuousPathInput w t i) :=
  (w i).continuous.comp continuous_real_toNNReal

@[simp] theorem continuousPathInput_nonneg {I : Type u_3}
    (w : I → C(ℝ≥0, ℝ)) (t : ℝ≥0) (i : I) :
    continuousPathInput w t i = w i t := by
  simp [continuousPathInput]

@[simp] theorem continuousPathInput_nat {I : Type u_4}
    (w : I → C(ℝ≥0, ℝ)) (n : ℕ) (i : I) :
    continuousPathInput w n i = w i n := by
  simp [continuousPathInput]

theorem continuousPathInput_leftTranslate {Γ : Type u_5} [Group Γ]
    (g : Γ) (w : Γ → C(ℝ≥0, ℝ)) (t : ℝ) :
    continuousPathInput (leftTranslate g w) t =
      leftTranslate g (continuousPathInput w t) := rfl

variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

theorem measurable_continuousPathInput {I : Type u_6} :
    Measurable (Function.uncurry (@continuousPathInput I)) := by
  apply Measurable.of_eval
  intro i
  exact continuous_eval.measurable.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      (continuous_real_toNNReal.measurable.comp measurable_snd))

end Problem336AdditiveD139

end

end OAI
