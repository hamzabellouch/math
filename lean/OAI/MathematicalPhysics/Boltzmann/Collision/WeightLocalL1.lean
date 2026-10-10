import OAI.MathematicalPhysics.Boltzmann.Branching.ChartPointLift
import OAI.MathematicalPhysics.Boltzmann.Branching.VaryingBoundedMultiplier
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight

namespace OAI

section

/-! # A positive lower bound for the hot weight on bounded velocity sets -/

noncomputable section

namespace BoltzmannNonuniqueness.VelocityWeight

def compactLower (R : ℝ) : ℝ :=
  Real.exp (-R^2)*(1+R^2)^(-50 : ℝ)

theorem compactLower_pos (R : ℝ) : 0 < compactLower R :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

theorem compactLower_le_H (q : ℝ) {R : ℝ} (hR : 0 ≤ R) {v : Velocity}
    (hv : ‖v‖ ≤ R) : compactLower R ≤ H q v := by
  have hs : ‖v‖^2 ≤ R^2 := sq_le_sq₀ (norm_nonneg v) hR |>.mpr hv
  have he : Real.exp (-R^2) ≤ Real.exp (-‖v‖^2) := Real.exp_le_exp.mpr (neg_le_neg hs)
  have hp : (1+R^2)^(-50 : ℝ) ≤ (1+‖v‖^2)^(-50 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  unfold compactLower H
  calc
    _ ≤ Real.exp (-‖v‖^2)*(1+‖v‖^2)^(-50 : ℝ) :=
      mul_le_mul he hp (by positivity) (by positivity)
    _ ≤ _ := le_mul_of_one_le_right (by positivity)
      (by linarith [singularity_nonneg q (transverse v)])

theorem inv_H_le_compactLower (q : ℝ) {R : ℝ} (hR : 0 ≤ R) {v : Velocity}
    (hv : ‖v‖ ≤ R) : (H q v)⁻¹ ≤ (compactLower R)⁻¹ :=
  inv_anti₀ (compactLower_pos R) (compactLower_le_H q hR hv)

end BoltzmannNonuniqueness.VelocityWeight

end

end

section

/-! # Bounds for the normalized weight on retained nonaxial velocities -/

noncomputable section

namespace BoltzmannNonuniqueness.VelocityWeight

theorem H_le_offAxis {q b : ℝ} (hq : 0 ≤ q) (hb : 0 < b)
    {v : Velocity} (hv : b ≤ ‖transverse v‖) : H q v ≤ 1+b^(-q) := by
  have hs : singularity q (transverse v) ≤ b^(-q) :=
    Real.rpow_le_rpow_of_nonpos hb hv (neg_nonpos.mpr hq)
  have he : Real.exp (-‖v‖^2) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg ‖v‖))
  have hp : (1+‖v‖^2)^(-50 : ℝ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) ≤ 1+‖v‖^2 by nlinarith [sq_nonneg ‖v‖]) (by norm_num : (-50 : ℝ) ≤ 0)
    simpa using h
  unfold H
  calc
    _ ≤ 1*(1+singularity q (transverse v)) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul he hp (by positivity) (by norm_num)).trans_eq (one_mul 1))
        (by linarith [singularity_nonneg q (transverse v)])
    _ ≤ 1+b^(-q) := by simpa using add_le_add_left hs 1

theorem H_ratio_le_offAxis {q b V : ℝ} (hq : 0 ≤ q) (hb : 0 < b) (hV : 0 ≤ V)
    {v ξ : Velocity} (hv : ‖v‖ ≤ V) (hξ : b ≤ ‖transverse ξ‖) :
    H q ξ/H q v ≤ (1+b^(-q))/compactLower V := by
  exact (div_le_div_of_nonneg_right (H_le_offAxis hq hb hξ) (H_pos q v).le).trans
    (div_le_div_of_nonneg_left (by positivity) (compactLower_pos V) (compactLower_le_H q hV hv))

end BoltzmannNonuniqueness.VelocityWeight

end

end

section

/-! # Division by the hot weight preserves local L1 vanishing -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure (X × Velocity)}

theorem tendsto_L1_div_H_on_velocity_ball {f : ℕ → X × Velocity → ℝ}
    (hm : ∀ n, Measurable (f n))
    (hL : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0))
    (q : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun z => f n z / VelocityWeight.H q z.2) 1
      (μ.restrict {z | ‖z.2‖ ≤ R})) atTop (𝓝 0) := by
  let ν := μ.restrict {z | ‖z.2‖ ≤ R}
  have hsmall : Tendsto (fun n => eLpNorm (f n) 1 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun _ => bot_le) (fun n => eLpNorm_mono_measure (f n) Measure.restrict_le_self)
  have hInv : Measurable (fun z : X × Velocity => (VelocityWeight.H q z.2)⁻¹) :=
    (ChartKernel.measurable_H q).inv.comp measurable_snd
  have hb : ∀ᵐ z ∂ν, |(VelocityWeight.H q z.2)⁻¹| ≤ (VelocityWeight.compactLower R)⁻¹ := by
    filter_upwards [ae_restrict_mem
      (measurableSet_le measurable_snd.norm measurable_const)] with z hz
    rw [abs_of_pos (inv_pos.mpr (VelocityWeight.H_pos q z.2))]
    exact VelocityWeight.inv_H_le_compactLower q hR hz
  have ht := tendsto_L1_bounded_mul_zero
    (fun n => (hm n).aestronglyMeasurable) (fun _ => hInv.aestronglyMeasurable)
    hsmall (inv_nonneg.mpr (VelocityWeight.compactLower_pos R).le)
    (Eventually.of_forall (fun _ => hb))
  simpa only [div_eq_mul_inv,mul_comm] using ht

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
