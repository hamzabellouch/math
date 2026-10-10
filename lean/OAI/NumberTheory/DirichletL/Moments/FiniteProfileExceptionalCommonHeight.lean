import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonSource
import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentExceptionalAmplitudePair CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentHeckeWindowEnergy
open HeckeFamily CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
universe u

def mass {lo hi:ℝ} (R:Finset (ℕ×ℕ)) {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Profiles lo hi)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):ℝ:=
  p.control R*q.control R*heightCost t₁ θ₁^J*heightCost t₂ θ₂^J*
    slotControl s.toData*slotControl v.toData*
    Real.sqrt (volume s.toData)*Real.sqrt (volume v.toData)

theorem mass_nonneg {lo hi:ℝ} (R:Finset (ℕ×ℕ)) {ι κ:Type u}[Fintype ι][Fintype κ]
    (s:Input ι)(v:Input κ)(p q:Profiles lo hi)(t₁ t₂ θ₁ θ₂:ℝ)(J:ℕ):
    0≤mass R s v p q t₁ t₂ θ₁ θ₂ J:=by
  have hp:=Profiles.control_nonneg p R
  have hq:=Profiles.control_nonneg q R
  have hs:=slotControl_nonneg s.toData
  have hv:=slotControl_nonneg v.toData
  have ht₁:=(heightCost_pos t₁ θ₁).le
  have ht₂:=(heightCost_pos t₂ θ₂).le
  unfold mass
  positivity

theorem shifted_mass {lo hi:ℝ} (R:Finset (ℕ×ℕ))
    {ι κ:Type u}[Fintype ι][Fintype κ][DecidableEq ι][DecidableEq κ]
    (s:Input ι)(v:Input κ)(η τ:Character)(p q:Profiles lo hi)(t₁ t₂ θ₁ θ₂ u w:ℝ)(J:ℕ):
    profileMass R (withHeight s η (t₁+2*Real.pi*(u-θ₁))).toData
      (withHeight v τ (t₂+2*Real.pi*(w-θ₂))).toData p q J≤
      mass R s v p q t₁ t₂ θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J:=by
  have hp:=pow_le_pow_left₀ (by positivity) (norm_height_shift t₁ θ₁ u) J
  have hq:=pow_le_pow_left₀ (by positivity) (norm_height_shift t₂ θ₂ w) J
  have hh:=mul_le_mul hp hq (by positivity)
    (pow_nonneg (mul_nonneg (heightCost_pos t₁ θ₁).le (by positivity)) _)
  have hcontrol:=mul_nonneg (Profiles.control_nonneg p R) (Profiles.control_nonneg q R)
  have hs:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hcontrol)
        (slotControl_nonneg s.toData))
      (slotControl_nonneg v.toData)) (Real.sqrt_nonneg (volume s.toData)))
      (Real.sqrt_nonneg (volume v.toData))
  convert hs using 1
  · dsimp only [profileMass,withHeight,slotControl,volume]
    ring
  · simp only [mass,mul_pow]
    ring
end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
