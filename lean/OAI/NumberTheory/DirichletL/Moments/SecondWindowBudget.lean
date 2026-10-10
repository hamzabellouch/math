import OAI.NumberTheory.DirichletL.Moments.SecondWindowSource

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowBudget
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentSecondWindowSource

def profileMoment (J : ℕ) : ℝ :=
  ∫ w : ℝ,(1+‖w‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖

theorem profileMoment_nonneg (J : ℕ) : 0≤profileMoment J :=
  integral_nonneg (fun w=>by positivity)

def heightEnvelope (t : ℝ) : ℝ := (1+‖t‖+2*Real.pi)*(1+2*Real.pi)

theorem heightEnvelope_pos (t : ℝ) : 0<heightEnvelope t := by unfold heightEnvelope;positivity

theorem heightCost_le_envelope (t θ : ℝ) : heightCost t θ≤heightEnvelope t*(1+‖θ‖) := by
  have hh : 1+‖t‖+2*Real.pi*‖θ‖≤(1+‖t‖+2*Real.pi)*(1+‖θ‖) := by
    nlinarith [norm_nonneg t,norm_nonneg θ,Real.pi_pos]
  have he := mul_le_mul_of_nonneg_right hh (show 0≤1+2*Real.pi by positivity)
  convert he using 1 <;> simp only [heightCost,heightEnvelope] ; ring

def windowBudget (J : ℕ) (t E : ℝ) : ℝ := Real.sqrt E*heightEnvelope t^J*profileMoment J

theorem windowBudget_nonneg (J : ℕ) (t E : ℝ) : 0≤windowBudget J t E :=
  mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (heightEnvelope_pos _).le _))
    (profileMoment_nonneg _)

theorem shifted_window_budget (J : ℕ) (t θ E : ℝ) (hE : 0≤E) :
    (E*heightCost t θ^(2*J))*profileMoment J^2≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  calc
    _ ≤ E*(heightEnvelope t*(1+‖θ‖))^(2*J)*profileMoment J^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (heightCost_pos _ _).le (heightCost_le_envelope t θ) _) hE)
        (sq_nonneg _)
    _ = _ := by
      rw [show 2*J=J*2 by omega,pow_mul]
      simp only [windowBudget,mul_pow,Real.sq_sqrt hE]
      ring

theorem conjugate_shifted_window_budget (J : ℕ) (t θ E : ℝ) (hE : 0≤E) :
    (E*heightCost t (-θ)^(2*J))*profileMoment J^2≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  simpa only [norm_neg] using shifted_window_budget J t (-θ) E hE

end SevenEighths.CenteredMomentSecondWindowBudget

end

end OAI
