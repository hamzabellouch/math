import OAI.Probability.InvariantIsing.Fields.FieldAdjacentOrder
import OAI.Probability.InvariantIsing.Fields.FieldTerminalGenerator

namespace OAI

/-! The final covariance coordinate has the same mixed monotonicity;
its backward derivative has the additional constant one half. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldTerminalFamily (a ζ : ℝ) : FieldSmoothFamily (Ioi (-a)) :=
  (fieldLogCoshFamily (Ioi (-a))).transform isOpen_Ioi a 1 ζ (fun t ht => by
    have h : -a < t := ht
    linarith)

lemma fieldTerminalFamily_value_eq_operator (a ζ t : ℝ) :
    (fun z => (fieldTerminalFamily a ζ).U (t, z)) =
      gaussianOperator ζ (Real.toNNReal (a + t)) (fun y => Real.log (Real.cosh y)) := by
  funext z
  change gaussianTransform (a + 1 * t) ζ (fun y => Real.log (Real.cosh y)) z = _
  rw [one_mul, field_gaussianTransform_eq_operator]

lemma fieldTerminalFamily_mean_eq_transition (a ζ t : ℝ) :
    (fun z => (fieldTerminalFamily a ζ).X (t, z)) =
      fieldSpinTransition ζ (Real.toNNReal (a + t))
        (fun y => Real.log (Real.cosh y)) Real.tanh := by
  have hm : Measurable (fun y : ℝ => Real.tanh y) := by
    simp only [Real.tanh_eq]
    fun_prop
  funext z
  change gaussianTiltAverage (a + 1 * t) ζ (fun y => Real.log (Real.cosh y)) Real.tanh z = _
  rw [one_mul, field_gaussianTiltAverage_eq_transition _ _ measurable_logCosh hm]

theorem fieldTerminalFamily_tangent (a ζ t z : ℝ) :
    (fieldTerminalFamily a ζ).T (t, z) = (1 : ℝ) / 2 - (1 - ζ) / 2 *
      gaussianTiltAverage (a + t) ζ (fun y => Real.log (Real.cosh y))
        (fun y => (Real.tanh y) ^ 2) z := by
  have hm : Measurable (fun y : ℝ => 1 / (Real.cosh y) ^ 2 + ζ * (Real.tanh y) ^ 2) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hx : Measurable (fun y : ℝ => (Real.tanh y) ^ 2) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hgen := fieldSpinTransition_terminal_generator ζ (Real.toNNReal (a + t)) z
  rw [← field_gaussianTiltAverage_eq_transition (a + t) ζ measurable_logCosh hm,
    ← field_gaussianTiltAverage_eq_transition (a + t) ζ measurable_logCosh hx] at hgen
  change gaussianTiltAverage (a + 1 * t) ζ (fun y => Real.log (Real.cosh y)) (fun _ => 0) z +
      (1 : ℝ) / 2 * gaussianTiltAverage (a + 1 * t) ζ
        (fun y => Real.log (Real.cosh y))
        (fun y => 1 / (Real.cosh y) ^ 2 + ζ * (Real.tanh y) ^ 2) z = _
  rw [one_mul, field_gaussianTiltAverage_const _ _ measurable_logCosh logCosh_linearGrowth,
    hgen]
  ring

theorem fieldTerminalFamily_tangent_antitone (a ζ : ℝ) (hζ : ζ ≤ 1) (t : ℝ) :
    AntitoneOn (fun z => (fieldTerminalFamily a ζ).T (t, z)) (Ici 0) := by
  have he : Function.Even (fun y : ℝ => Real.log (Real.cosh y)) := by
    intro y
    simp only [Real.cosh_neg]
  have hm : Measurable (fun y : ℝ => Real.tanh y) := by
    simp only [Real.tanh_eq]
    fun_prop
  have h := field_negative_square_average_shape (a + t) ζ ((1 - ζ) / 2) (by linarith)
    measurable_logCosh he logCosh_linearGrowth hm Real.tanh_neg
    (field_tanh_monotone.monotoneOn _) (fun _ hy => field_tanh_nonneg hy)
    field_abs_tanh_le_one
  intro x hx y hy hxy
  dsimp only
  rw [fieldTerminalFamily_tangent, fieldTerminalFamily_tangent]
  have hh := h.2 hx hy hxy
  dsimp only at hh
  linarith

theorem fieldTerminalFamily_shape (a ζ : ℝ) (hζ : 0 ≤ ζ) (t : ℝ) :
    Function.Even (fun z => (fieldTerminalFamily a ζ).U (t, z)) ∧
    Function.Odd (fun z => (fieldTerminalFamily a ζ).X (t, z)) ∧
    MonotoneOn (fun z => (fieldTerminalFamily a ζ).X (t, z)) (Ici 0) ∧
    (∀ z ∈ Ici (0 : ℝ), 0 ≤ (fieldTerminalFamily a ζ).X (t, z)) ∧
    (∀ z, |(fieldTerminalFamily a ζ).X (t, z)| ≤ 1) := by
  have he : Function.Even (fun y : ℝ => Real.log (Real.cosh y)) := by
    intro y
    simp only [Real.cosh_neg]
  have hm : Measurable (fun y : ℝ => Real.tanh y) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hval := fieldTerminalFamily_value_eq_operator a ζ t
  have hmean := fieldTerminalFamily_mean_eq_transition a ζ t
  have hmeanPoint (z : ℝ) := congrFun hmean z
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hval]
    exact gaussianOperator_even ζ _ measurable_logCosh he
  · rw [hmean]
    exact fieldSpinTransition_odd ζ _ measurable_logCosh he hm Real.tanh_neg
  · rw [hmean]
    exact fieldSpinTransition_monotone hζ _ measurable_logCosh he logCosh_linearGrowth
      hm Real.tanh_neg (field_tanh_monotone.monotoneOn _)
      (fun _ hz => field_tanh_nonneg hz) field_abs_tanh_le_one
  · intro z hz
    rw [hmeanPoint]
    exact fieldSpinTransition_nonneg ζ _ measurable_logCosh he logCosh_linearGrowth
      hm Real.tanh_neg (fun _ hy => field_tanh_nonneg hy) field_abs_tanh_le_one hz
  · intro z
    rw [hmeanPoint]
    exact fieldSpinTransition_bound ζ _ measurable_logCosh logCosh_linearGrowth
      field_abs_tanh_le_one z

theorem fieldTerminal_earlier_squares_antitone (a ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (P : List (ℝ × ℝ≥0)) (hP : ∀ av ∈ P, 0 < av.1)
    {t s : ℝ} (ht : t ∈ Ioi (-a)) (hs : s ∈ Ioi (-a)) (hts : t ≤ s) :
    let G := fieldTerminalFamily a ζ
    ∀ i z, fieldScalarSquares P (fun y => G.U (s, y)) (fun y => G.X (s, y)) i z ≤
      fieldScalarSquares P (fun y => G.U (t, y)) (fun y => G.X (t, y)) i z := by
  have hshape (q : ℝ) := fieldTerminalFamily_shape a ζ hζ0 q
  exact (fieldTerminalFamily a ζ).earlier_squares_antitone_parameter (convex_Ioi (-a))
    (fun q _ => fieldTerminalFamily_tangent_antitone a ζ hζ1 q)
    (fun q _ => (hshape q).1) (fun q _ => (hshape q).2.1)
    (fun q _ => (hshape q).2.2.1) (fun q _ => (hshape q).2.2.2.1)
    (fun p => (hshape p.1).2.2.2.2 p.2) P hP ht hs hts

end InvariantIsing

end

end OAI
