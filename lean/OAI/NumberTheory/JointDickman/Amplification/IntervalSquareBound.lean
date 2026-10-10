import OAI.NumberTheory.JointDickman.Probability.ResidueFourierParseval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # The local-window Cauchy inequality used by residue histograms -/

namespace JointDickman
open MeasureTheory

theorem interval_integral_square_le {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun x => (f x)^2) volume a b) :
    (∫ x in a..b, f x)^2 ≤ (b-a)*(∫ x in a..b, (f x)^2) := by
  by_cases heq : a = b
  · subst b
    simp
  have hL : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne hab heq)
  let I := ∫ x in a..b, f x
  let m := I/(b-a)
  have hv : 0 ≤ ∫ x in a..b, (f x-m)^2 :=
    intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
  have he : (∫ x in a..b, (f x-m)^2) =
      (∫ x in a..b, (f x)^2)-2*m*I+m^2*(b-a) := by
    have hfun : (fun x => (f x-m)^2) = (fun x => (f x)^2-(2*m)*f x+m^2) := by
      funext x
      ring
    rw [hfun,intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hf.const_mul _),intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [he] at hv
  have hm : m*(b-a) = I := div_mul_cancel₀ I hL.ne'
  have hh := mul_nonneg hv hL.le
  dsimp [I] at hm hh ⊢
  nlinarith

theorem interval_norm_integral_square_le {a b : ℝ} {F : ℝ → ℂ} (hab : a ≤ b)
    (hF : IntervalIntegrable F volume a b)
    (hF2 : IntervalIntegrable (fun x => ‖F x‖^2) volume a b) :
    ‖∫ x in a..b, F x‖^2 ≤ (b-a)*(∫ x in a..b, ‖F x‖^2) := by
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab (f := F)
  have hnonneg : 0 ≤ ∫ x in a..b, ‖F x‖ :=
    intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
  exact ((sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hnorm).trans
    (interval_integral_square_le hab hF.norm hF2)

end JointDickman

end OAI
