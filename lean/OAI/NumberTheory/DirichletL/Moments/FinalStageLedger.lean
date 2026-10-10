import OAI.NumberTheory.DirichletL.Moments.DescentLedger

namespace OAI

noncomputable section
namespace SevenEighths.CenteredMomentFinalStageLedger

theorem capped_loss (M v : ℝ) : M/6≤2*v/3+max (M/4-v) 0 := by
  by_cases h : 0≤M/4-v
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem final_exponent (A M v loss₁ loss₂ : ℝ) :
    A-5*M/6-2*v/3-max (M/4-v) 0+loss₁+loss₂≤
      max (A-M) 0+loss₁+loss₂ := by
  have h:=capped_loss M v
  have hm:=le_max_left (A-M) (0:ℝ)
  linarith

theorem saving_exponent (A M v F₁ F₂ loss₁ loss₂ : ℝ)
    (h₁:2*v/3-loss₁≤F₁) (h₂:max (M/4-v) 0-loss₂≤F₂) :
    A-5*M/6-F₁-F₂≤max (A-M) 0+loss₁+loss₂ := by
  linarith [final_exponent A M v loss₁ loss₂]

theorem saving_power (Z A M v F₁ F₂ loss₁ loss₂ : ℝ) (hZ:1≤Z)
    (h₁:2*v/3-loss₁≤F₁) (h₂:max (M/4-v) 0-loss₂≤F₂) :
    Z^(A-5*M/6-F₁-F₂)≤Z^(max (A-M) 0+loss₁+loss₂) :=
  Real.rpow_le_rpow_of_exponent_le hZ (saving_exponent A M v F₁ F₂ loss₁ loss₂ h₁ h₂)

end SevenEighths.CenteredMomentFinalStageLedger

end

end OAI
