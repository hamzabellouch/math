import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSource
import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalHeight
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentHeckeWindowEnergy HeckeFamily CenteredMomentAllocatedDetectorAmplitude
universe u

def cost (p:Tests)(t θ:ℝ):ℝ:=‖p.height 0‖+‖p.height 1‖+heightCost t θ

theorem cost_pos (p:Tests)(t θ:ℝ):0<cost p t θ:=by
  dsimp only [cost]
  linarith [norm_nonneg (p.height 0),norm_nonneg (p.height 1),heightCost_pos t θ]

theorem shifted_weight (p:Tests)(t θ u:ℝ):
    p.heightWeight (t+2*Real.pi*(u-θ))≤cost p t θ*(1+‖u‖):=by
  have h:=norm_height_shift t θ u
  dsimp only [Tests.heightWeight,cost]
  nlinarith [mul_nonneg (norm_nonneg (p.height 0)) (norm_nonneg u),
    mul_nonneg (norm_nonneg (p.height 1)) (norm_nonneg u)]

def mass {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):ℝ:=
  cost p t₁ θ₁^J*cost q t₂ θ₂^J*slotControl s.toData*slotControl v.toData*
    Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData)

theorem mass_nonneg {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Tests)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):
    0≤mass s v p q t₁ t₂ θ₁ θ₂ J:=by
  unfold mass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (pow_nonneg (cost_pos p t₁ θ₁).le _) (pow_nonneg (cost_pos q t₂ θ₂).le _))
    (slotControl_nonneg _)) (slotControl_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem shifted_mass {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(η τ:Character)(p q:Tests)(t₁ t₂ θ₁ θ₂ u w:ℝ)(J:ℕ):
    profileMass (withHeight s η (t₁+2*Real.pi*(u-θ₁))).toData
      (withHeight v τ (t₂+2*Real.pi*(w-θ₂))).toData p q J≤
      mass s v p q t₁ t₂ θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J:=by
  have hp:=pow_le_pow_left₀ (by dsimp [Tests.heightWeight];positivity)
    (shifted_weight p t₁ θ₁ u) J
  have hq:=pow_le_pow_left₀ (by dsimp [Tests.heightWeight];positivity)
    (shifted_weight q t₂ θ₂ w) J
  have hh:=mul_le_mul hp hq (by dsimp [Tests.heightWeight];positivity)
    (pow_nonneg (mul_nonneg (cost_pos p t₁ θ₁).le (by positivity)) _)
  have hs:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (slotControl_nonneg s.toData))
      (slotControl_nonneg v.toData)) (Real.sqrt_nonneg (volume s.toData)))
      (Real.sqrt_nonneg (volume v.toData))
  convert hs using 1
  · rfl
  · simp only [mass,mul_pow];ring

end SevenEighths.CenteredMomentExceptionalHeight

end

end OAI
