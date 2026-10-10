import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyCongrAe
import OAI.Geometry.WeakHessian.LocalBounds.SlopeApproxAntitone

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X]
variable [MeasurableSpace X] {m : Measure X}
attribute [local instance] Classical.propDecidable
omit [MeasurableSpace X] in
lemma GloballyLipschitz.const_mul {f : X → ℝ} (hf : GloballyLipschitz f) (c : ℝ) :
    GloballyLipschitz (fun x => c * f x) := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨‖c‖₊ * L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  simpa only [mul_assoc, Real.dist_eq] using
    mul_le_mul_of_nonneg_left (hL.dist_le_mul x y) (abs_nonneg c)

lemma cheegerEnergy_zero : cheegerEnergy m (fun _ : X => (0:ℝ)) = 0 := by
  apply le_antisymm _ bot_le
  change cheegerEnergy m (fun _ : X => (0:ℝ)) ≤ 0
  have hh := cheegerEnergy_le_liminf (MemLp.zero' (μ := m))
    (fs := fun _ _ => (0:ℝ)) (fun _ => ⟨⟨0, by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp⟩, MemLp.zero'⟩) (by simp)
  simpa only [localSlope_zero, zero_pow (by omega : (2:ℕ) ≠ 0),
    lintegral_zero, mul_zero, liminf_const] using hh

lemma cheegerEnergy_const_mul_le (c : ℝ) (f : X → ℝ) :
    cheegerEnergy m (fun x => c * f x) ≤ ENNReal.ofReal (c^2) * cheegerEnergy m f := by
  by_cases hc : c = 0
  · subst c
    simp only [zero_mul, zero_pow (by omega : (2:ℕ) ≠ 0), ENNReal.ofReal_zero,
      cheegerEnergy_zero, le_refl]
  have hC0 : ENNReal.ofReal (c^2) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hc))
  by_cases he : cheegerEnergy m f = ∞
  · simp only [he, ENNReal.mul_top hC0, le_top]
  have hf : MemLp f 2 m := by
    by_contra H
    exact he (by simp only [cheegerEnergy, ite_eq_right H])
  let S : Set ℝ≥0∞ := {a | ∃ fs : ℕ → X → ℝ,
      (∀ n, GloballyLipschitz (fs n) ∧ MemLp (fs n) 2 m) ∧
      Tendsto (fun n => eLpNorm (fun x => fs n x - f x) 2 m) atTop (𝓝 0) ∧
      a = liminf (fun n => (2:ℝ≥0∞)⁻¹ * ∫⁻ x, localSlope (fs n) x ^ 2 ∂m) atTop}
  have hE : cheegerEnergy m f = sInf S := by simp only [cheegerEnergy, ite_eq_left hf, S]
  have hS : S.Nonempty := by
    by_contra H
    rw [Set.not_nonempty_iff_eq_empty.mp H, sInf_empty] at hE
    exact he hE
  let : Nonempty S := hS.to_subtype
  rw [hE, sInf_eq_iInf', ENNReal.mul_iInf (fun h => (ENNReal.ofReal_ne_top h).elim)]
  apply le_iInf
  intro a
  obtain ⟨fs, hfs, hconv, ha⟩ := a.property
  have hfC : MemLp (fun x => c * f x) 2 m := hf.const_mul c
  have hcconv : Tendsto (fun n => eLpNorm (fun x => c * fs n x - c * f x) 2 m)
      atTop (𝓝 0) := by
    simp_rw [← mul_sub]
    change Tendsto (fun n => eLpNorm (c • (fun x => fs n x - f x)) 2 m) atTop (𝓝 0)
    simp_rw [eLpNorm_const_smul]
    simpa only [mul_zero, Function.comp_def] using (ENNReal.continuous_const_mul (show ‖c‖ₑ ≠ ∞ by finiteness)).tendsto 0 |>.comp hconv
  have hmain := cheegerEnergy_le_liminf hfC
    (fun n => ⟨(hfs n).1.const_mul c, (hfs n).2.const_mul c⟩) hcconv
  refine hmain.trans_eq ?_
  simp_rw [slope_energy_const_mul]
  rw [ha]
  exact (Monotone.map_liminf_of_continuousAt
    (f := fun a : ℝ≥0∞ => ENNReal.ofReal (c^2) * a)
    (fun _ _ h => mul_le_mul_right h _) _
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousAt).symm

lemma cheegerEnergy_const_mul (c : ℝ) (f : X → ℝ) :
    cheegerEnergy m (fun x => c * f x) = ENNReal.ofReal (c^2) * cheegerEnergy m f := by
  apply le_antisymm (cheegerEnergy_const_mul_le c f)
  by_cases hc : c = 0
  · simp [hc]
  have H := cheegerEnergy_const_mul_le (m := m) c⁻¹ (fun x => c * f x)
  simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at H
  have H' := mul_le_mul_right H (ENNReal.ofReal (c^2))
  have hcancel : ENNReal.ofReal (c^2) * ENNReal.ofReal (c⁻¹^2) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg c), ← mul_pow, mul_inv_cancel₀ hc, one_pow,
      ENNReal.ofReal_one]
  simpa only [← mul_assoc, hcancel, one_mul] using H'

end WeakHessian

end
end InlinedFile0

end OAI
