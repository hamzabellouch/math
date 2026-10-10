import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource
import OAI.NumberTheory.DirichletL.Dictionary.InverseUniformScale
import OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff FourierTransform

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open CenteredMomentRetainedProfile CenteredMomentAllocatedNaturalSource
open EisensteinSchwartzPoisson CenteredMomentLattice

def sourcePlain (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) : Plain :=
  ⟨W,a,b,ha,hs,W.smooth ⊤⟩

theorem sourcePlain_support (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (U:ℝ) (hU:0<U) (t:ℝ) :
    Function.support ((sourcePlain a b ha W hs).profile U hU t:ℝ→ℂ)⊆
      Set.Icc (a/max 1 b) b := by
  by_cases hret:1≤U*b
  · rw [Plain.profile_retained _ U hU t hret]
    exact retainedProfile_support W a b ha hs (W.smooth ⊤) U hU hret t
  · rw [Plain.profile_zero _ U hU t (lt_of_not_ge hret)]
    simp

theorem plain_profile_source_control (a b:ℝ) (ha:0<a) (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      ∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀U:ℝ,∀hU:0<U,∀t:ℝ,
      sourceControl S ((sourcePlain a b ha W hs).profile U hU t)≤
        C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hsource⟩ := normPowerProfile_source_control a b ha S
  refine ⟨n,T,(max 1 b)^(S.sup Prod.snd)*C,by positivity,?_⟩
  intro W hs U hU t
  have hp:=sourceControl_nonneg T W
  by_cases hret:1≤U*b
  · rw [Plain.profile_retained _ U hU t hret]
    have hd:=normPowerProfile_dilated_finite W a b (max 1 b) (clipDilation U)
      ha (le_max_left _ _) (clipDilation_ge_one U hU) (clipDilation_le b U hU hret)
      hs (W.smooth ⊤) t S
    exact hd.trans ((mul_le_mul_of_nonneg_left (hsource W hs t) (by positivity)).trans_eq (by dsimp only [sourceControl]; ring))
  · rw [Plain.profile_zero _ U hU t (lt_of_not_ge hret)]
    simpa only [sourceControl,map_zero] using
      (show 0≤(max 1 b)^(S.sup Prod.snd)*C*sourceControl T W*(1+‖t‖)^n by positivity)

theorem scale_source_control (S:Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      sourceControl S (DetectorDictionaryInverseUniform.scaleCLM W)≤C*sourceControl T W :=
  schwartzCLM_finite_seminorm_control DetectorDictionaryInverseUniform.scaleCLM S

theorem scale_source_support (a b:ℝ) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) :
    Function.support (DetectorDictionaryInverseUniform.scaleCLM W:ℝ→ℂ)⊆Set.Icc a b := by
  have he:(DetectorDictionaryInverseUniform.scaleCLM W:ℝ→ℂ)=
      HeckeInverseAmplification.scaleProfile W :=
    funext (DetectorDictionaryInverseUniform.scaleCLM_apply W)
  rw [he]
  exact HeckeInverseAmplification.scaleProfile_support W a b hs

theorem fourier_source_control (S:Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      sourceControl S (FourierTransform.fourierCLM ℝ (𝓢(ℝ,ℂ)) W)≤C*sourceControl T W :=
  schwartzCLM_finite_seminorm_control (FourierTransform.fourierCLM ℝ (𝓢(ℝ,ℂ))) S

def logWindowMultiply : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ
    (CenteredMomentReflectedAnnuli.logWindowSchwartz:ℝ→ℂ)).restrictScalars ℝ

theorem logWindowMultiply_apply (W:𝓢(ℝ,ℂ)) (x:ℝ) :
    logWindowMultiply W x=CenteredMomentReflectedAnnuli.logWindow x*W x := by
  change (SchwartzMap.smulLeftCLM ℂ
    (CenteredMomentReflectedAnnuli.logWindowSchwartz:ℝ→ℂ) W) x=_
  rw [SchwartzMap.smulLeftCLM_apply_apply
    CenteredMomentReflectedAnnuli.logWindowSchwartz.hasTemperateGrowth]
  rfl

theorem logWindow_source_control (S:Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      sourceControl S (logWindowMultiply W)≤C*sourceControl T W :=
  schwartzCLM_finite_seminorm_control logWindowMultiply S

theorem window_fourier_twist_source_control (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),∀t:ℝ,
      sourceControl S (FourierTransform.fourierCLM ℝ (𝓢(ℝ,ℂ))
        (logWindowMultiply (JointLogSeparation.frequencyTwist W t)))≤
      C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩:=fourier_source_control S
  obtain ⟨S₂,C₂,hC₂,h₂⟩:=logWindow_source_control S₁
  obtain ⟨n,T,C₃,hC₃,h₃⟩:=frequencyTwist_source_control S₂
  refine ⟨n,T,C₁*C₂*C₃,by positivity,?_⟩
  intro W t
  exact (h₁ _).trans ((mul_le_mul_of_nonneg_left
    ((h₂ _).trans (mul_le_mul_of_nonneg_left (h₃ W t) hC₂.le)) hC₁.le).trans_eq (by dsimp only [sourceControl]; ring))

theorem scaled_plain_profile_source_control (a b:ℝ) (ha:0<a) (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      ∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀U:ℝ,∀hU:0<U,∀t:ℝ,
      sourceControl S (DetectorDictionaryInverseUniform.scaleCLM
        ((sourcePlain a b ha W hs).profile U hU t))≤
        C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩:=scale_source_control S
  obtain ⟨n,T,C₂,hC₂,h₂⟩:=plain_profile_source_control a b ha S₁
  refine ⟨n,T,C₁*C₂,by positivity,?_⟩
  intro W hs U hU t
  exact (h₁ _).trans ((mul_le_mul_of_nonneg_left (h₂ W hs U hU t) hC₁.le).trans_eq (by ring))

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
