import OAI.NumberTheory.CubicMoment.Estimates.LongPrimePowers

namespace OAI

/-! The long-prime threshold gives the actual logarithmic parameter
range required by the published prime estimate, even after bin dilation. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem long_prime_logarithmic_window {P₀ : ℝ} (hP₀ : 1 < P₀) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X/4 ∧
      ∀ P : ℝ, Real.exp (Real.sqrt (Real.log X))/2 ≤ P →
        P₀ ≤ P ∧ Real.log X/4 ≤ (Real.log P)^2 := by
  have ht : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop
    (max (2*Real.log 2) (Real.log (2*P₀)))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4:ℝ))] with X hroot hL
  have hroot₂ : 2*Real.log 2 ≤ Real.sqrt (Real.log X) := (le_max_left _ _).trans hroot
  have hrootP : Real.log (2*P₀) ≤ Real.sqrt (Real.log X) := (le_max_right _ _).trans hroot
  refine ⟨by linarith,?_⟩
  intro P hP
  have hPpos : 0 < P := (div_pos (Real.exp_pos _) (by norm_num)).trans_le hP
  have hP₀pos : 0 < 2*P₀ := by linarith
  refine ⟨?_,?_⟩
  · calc
      P₀ = Real.exp (Real.log (2*P₀))/2 := by rw [Real.exp_log hP₀pos]; ring
      _ ≤ Real.exp (Real.sqrt (Real.log X))/2 :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hrootP) (by norm_num)
      _ ≤ P := hP
  · have hlog : Real.sqrt (Real.log X)-Real.log 2 ≤ Real.log P := by
      have h := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num)) hP
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num),Real.log_exp] at h
      exact h
    have hhalf : Real.sqrt (Real.log X)/2 ≤ Real.log P := by linarith
    have hlog₀ : 0 ≤ Real.log P := (by positivity : 0 ≤ Real.sqrt (Real.log X)/2).trans hhalf
    have hprod := mul_nonneg (sub_nonneg.mpr hhalf)
      (add_nonneg hlog₀ (by positivity : 0 ≤ Real.sqrt (Real.log X)/2))
    have hsqrt := Real.sq_sqrt (show 0 ≤ Real.log X by linarith)
    nlinarith

end CubicFirstMoment

end

end OAI
