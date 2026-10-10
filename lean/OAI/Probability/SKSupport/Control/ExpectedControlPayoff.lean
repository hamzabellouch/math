import Mathlib
import OAI.Probability.SKSupport.Regularity.AbsExtend

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

lemma expected_controlPayoff_le (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    (∫ ω, controlPayoff W γ t x α ω ∂W.law) ≤
      (∫ ω, |x + W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law) +
      (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s := by
  let := W.isProbability
  have hnoise : Integrable (fun ω => |x + W.B 1 ω - W.B (Real.toNNReal t) ω|) W.law :=
    (((integrable_const x).add (W.brownian.integrable_eval 1)).sub
      (W.brownian.integrable_eval (Real.toNNReal t))).abs
  calc
    _ ≤ ∫ ω, (|x + W.B 1 ω - W.B (Real.toNNReal t) ω| +
        (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s) ∂W.law :=
      integral_mono (controlPayoff_integrable W γ t x ht α)
        (hnoise.add (integrable_const _)) (controlPayoff_le W γ t x ht α)
    _ = _ := by rw [integral_add hnoise (integrable_const _)]; simp

lemma control_values_bddAbove (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) :
    BddAbove (Set.range (fun α : Control W (Real.toNNReal t) =>
      ∫ ω, controlPayoff W γ t x α ω ∂W.law)) := by
  refine ⟨(∫ ω, |x + W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law) +
      (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s, ?_⟩
  rintro _ ⟨α, rfl⟩
  exact expected_controlPayoff_le W γ t x ht α

lemma expected_controlPayoff_le_value (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) (α : Control W (Real.toNNReal t)) :
    (∫ ω, controlPayoff W γ t x α ω ∂W.law) ≤ value W γ t x := by
  exact le_csSup (control_values_bddAbove W γ t x ht) ⟨α, rfl⟩

lemma value_le_expected_abs (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) :
    value W γ t x ≤ (∫ ω, |x + W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law) +
      (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s := by
  unfold value
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨zeroControl W (Real.toNNReal t), rfl⟩⟩
  rintro _ ⟨α, rfl⟩
  exact expected_controlPayoff_le W γ t x ht α

lemma abs_le_value (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x : ℝ) (ht : t ≤ 1) : |x| ≤ value W γ t x := by
  let := W.isProbability
  have hmean : (∫ ω, (x + W.B 1 ω - W.B (Real.toNNReal t) ω) ∂W.law) = x := by
    have ha : Integrable (fun ω => x + W.B 1 ω) W.law :=
      (integrable_const x).add (W.brownian.integrable_eval 1)
    rw [integral_sub ha
      (W.brownian.integrable_eval (Real.toNNReal t)),
      integral_add (integrable_const x) (W.brownian.integrable_eval 1)]
    simp [W.brownian.integral_eval]
  calc
    |x| = |∫ ω, (x + W.B 1 ω - W.B (Real.toNNReal t) ω) ∂W.law| := by rw [hmean]
    _ ≤ ∫ ω, |x + W.B 1 ω - W.B (Real.toNNReal t) ω| ∂W.law :=
      abs_integral_le_integral_abs
    _ = ∫ ω, controlPayoff W γ t x (zeroControl W (Real.toNNReal t)) ω ∂W.law := by
      simp [controlPayoff, zeroControl]
    _ ≤ value W γ t x := expected_controlPayoff_le_value W γ t x ht _

lemma controlPayoff_space_le (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x y : ℝ) (α : Control W (Real.toNNReal t)) (ω : Ω) :
    controlPayoff W γ t x α ω ≤ controlPayoff W γ t y α ω + |x - y| := by
  have h := abs_add_le
    (y + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω) (x-y)
  have heq : y + W.B 1 ω - W.B (Real.toNNReal t) ω +
      (∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω) + (x-y) =
      x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω := by ring
  rw [heq] at h
  dsimp [controlPayoff]
  linarith

lemma value_space_le (W : BrownianSystem Ω) (γ : OrderParameter)
    (t x y : ℝ) (ht : t ≤ 1) : value W γ t x ≤ value W γ t y + |x - y| := by
  let := W.isProbability
  unfold value
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨zeroControl W (Real.toNNReal t), rfl⟩⟩
  rintro _ ⟨α, rfl⟩
  calc
    (∫ ω, controlPayoff W γ t x α ω ∂W.law) ≤
        ∫ ω, (controlPayoff W γ t y α ω + |x-y|) ∂W.law :=
      integral_mono (controlPayoff_integrable W γ t x ht α)
        ((controlPayoff_integrable W γ t y ht α).add (integrable_const _))
        (controlPayoff_space_le W γ t x y α)
    _ = (∫ ω, controlPayoff W γ t y α ω ∂W.law) + |x-y| := by
      rw [integral_add (controlPayoff_integrable W γ t y ht α) (integrable_const _)]
      simp
    _ ≤ value W γ t y + |x-y| :=
      add_le_add (expected_controlPayoff_le_value W γ t y ht α) le_rfl

theorem value_lipschitz (W : BrownianSystem Ω) (γ : OrderParameter)
    (t : ℝ) (ht : t ≤ 1) : LipschitzWith 1 (value W γ t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [abs_le]
  constructor
  · have h := value_space_le W γ t y x ht
    rw [abs_sub_comm y x] at h
    linarith
  · have h := value_space_le W γ t x y ht
    linarith

end ZeroTemperatureSK

end
end

end OAI
