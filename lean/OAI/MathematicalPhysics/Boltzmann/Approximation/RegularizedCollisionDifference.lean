import OAI.MathematicalPhysics.Boltzmann.Approximation.CutoffLipschitz
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers
import OAI.MathematicalPhysics.Boltzmann.Approximation.RegularizedLogBounds

namespace OAI

/-! # The cutoff collision error of positive Gaussian regularization -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetBarrierCollision

namespace BoltzmannNonuniqueness

def gaussianRegularization (δ : ℝ) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  f v+δ*Real.exp (-2*‖v‖^2)

theorem gaussianRegularization_measurable (δ : ℝ) {f : Velocity → ℝ} (hf : Measurable f) :
    Measurable (gaussianRegularization δ f) := by
  unfold gaussianRegularization
  fun_prop

theorem gaussianRegularization_pos {δ : ℝ} (hδ : 0 < δ) {f : Velocity → ℝ}
    (hf : ∀ v, 0 ≤ f v) (v : Velocity) : 0 < gaussianRegularization δ f v :=
  add_pos_of_nonneg_of_pos (hf v) (mul_pos hδ (Real.exp_pos _))

theorem gaussianRegularization_bound {δ A q : ℝ} (_hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    {f : Velocity → ℝ} (hf : ∀ v, f v ≤ A*H q v) (v : Velocity) :
    gaussianRegularization δ f v ≤ (A+tiltConstant)*H q v := by
  have he := JetGaussianEscape.gaussian_le_hot q v
  have hle : δ*Real.exp (-2*‖v‖^2) ≤ tiltConstant*H q v :=
    (mul_le_mul_of_nonneg_right hδone (Real.exp_nonneg _)).trans (by simpa using he)
  unfold gaussianRegularization
  nlinarith only [hf v,hle]

theorem gaussianRegularization_collision_error (hcarleman : Published.GPV2009CarlemanInput)
    {δ A q b : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hA : 0 ≤ A)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b)
    {f : Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ v, 0 ≤ f v)
    (hfb : ∀ v, f v ≤ A*H q v) :
    ∀ᵐ v : Velocity,
      |CutoffLipschitz.collision b (gaussianRegularization δ f) v-CutoffLipschitz.collision b f v| ≤
        δ*(tiltConstant*(2*A+tiltConstant)*
          (HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b))*H q v := by
  have hn : ∀ v, 0 ≤ gaussianRegularization δ f v :=
    fun v => add_nonneg (hfn v) (mul_nonneg hδ (Real.exp_nonneg _))
  have hd : ∀ v, |gaussianRegularization δ f v-f v| ≤ (δ*tiltConstant)*H q v := by
    intro v
    have he := mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q v) hδ
    simpa only [gaussianRegularization,add_sub_cancel_left,
      abs_of_nonneg (mul_nonneg hδ (Real.exp_nonneg _)),mul_assoc] using he
  have ht := CutoffLipschitz.collision_difference hcarleman hq₁ hq₂ hb
    (add_nonneg hA tiltConstant_pos.le) hA (mul_nonneg hδ tiltConstant_pos.le)
    (gaussianRegularization_measurable δ hfm) hfm hn hfn
    (gaussianRegularization_bound hδ hδone hfb) hfb hd
  filter_upwards [ht] with v hv
  convert hv using 1
  ring

end BoltzmannNonuniqueness

end

end OAI
