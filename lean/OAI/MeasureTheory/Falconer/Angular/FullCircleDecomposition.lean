import OAI.MeasureTheory.Falconer.Angular.CircleLocalIntegral
import OAI.MeasureTheory.Falconer.Angular.CircleResidualDecay

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem stationarySineCutoff_periodic : Function.Periodic
    (fun θ => stationaryCutoff (stationarySineChart θ)) (2*Real.pi) := by
  intro θ
  have he : (θ+2*Real.pi)/2 = θ/2+Real.pi := by ring
  simp only [stationarySineChart,he,Real.sin_add_pi,mul_neg]
  exact stationaryCutoff.neg _

 theorem stationaryCosineCutoff_periodic : Function.Periodic
    (fun θ => stationaryCutoff (stationaryCosineChart θ)) (2*Real.pi) := by
  intro θ
  have he : (θ+2*Real.pi)/2 = θ/2+Real.pi := by ring
  simp only [stationaryCosineChart,he,Real.cos_add_pi,mul_neg]
  exact stationaryCutoff.neg _

 theorem cosineOscillator_periodic (Λ : ℝ) : Function.Periodic (cosineOscillator Λ) (2*Real.pi) := by
  intro θ
  simp [cosineOscillator,Real.cos_add_two_pi]

 theorem stationaryCosineCutoff_add_pi (θ : ℝ) :
    stationaryCutoff (stationaryCosineChart (θ+Real.pi)) = stationaryCutoff (stationarySineChart θ) := by
  have he : (θ+Real.pi)/2 = θ/2+Real.pi/2 := by ring
  simp only [stationaryCosineChart,he,Real.cos_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
    mul_zero,mul_one,zero_sub,mul_neg,stationarySineChart]
  exact stationaryCutoff.neg _

 theorem cosineOscillator_add_pi (Λ θ : ℝ) :
    cosineOscillator Λ (θ+Real.pi) = cosineOscillator (-Λ) θ := by
  simp only [cosineOscillator,Real.cos_add_pi,Complex.ofReal_neg]
  congr 1
  ring

 theorem circle_negative_piece (Λ : ℝ) {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi)) :
    (∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ *
      (stationaryCutoff (stationaryCosineChart θ):ℂ)*f θ) =
      localizedCircleIntegral (-Λ) (fun θ => f (θ+Real.pi)) := by
  let G : ℝ → ℂ := fun θ => cosineOscillator Λ θ *
    (stationaryCutoff (stationaryCosineChart θ):ℂ)*f θ
  have hG : Function.Periodic G (2*Real.pi) := by
    intro θ
    simp only [G,cosineOscillator_periodic Λ θ,stationaryCosineCutoff_periodic θ,hp θ]
  have hs := hG.intervalIntegral_add_eq (-Real.pi) 0
  have he₁ : -Real.pi+2*Real.pi = Real.pi := by ring
  simp only [he₁,zero_add] at hs
  change (∫ θ in (-Real.pi)..Real.pi, G θ) = _
  rw [hs]
  have he₂ : (∫ θ in (-Real.pi)..Real.pi, G (θ+Real.pi)) = ∫ θ in (0:ℝ)..2*Real.pi, G θ := by
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  rw [← he₂]
  have hGF : (fun θ => G (θ+Real.pi)) = fun θ => cosineOscillator (-Λ) θ *
      (stationaryCutoff (stationarySineChart θ):ℂ)*f (θ+Real.pi) := by
    funext θ
    simp only [G,cosineOscillator_add_pi,stationaryCosineCutoff_add_pi]
  rw [hGF]
  exact circlePositivePiece_localized (-Λ) _

 theorem circle_residual_integral (Λ : ℝ) (f : ℝ → ℂ) :
    (∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ *
      (circleStationaryResidual θ:ℂ)*f θ) =
    ∫ θ : ℝ, cosineOscillator Λ θ * circleResidualAmplitude f θ := by
  let F : ℝ → ℂ := fun θ => cosineOscillator Λ θ * (circleStationaryResidual θ:ℂ)*f θ
  have hπ : circleStationaryResidual Real.pi = 0 := by
    apply circleStationaryResidual_zero_cosine
    simp [stationaryCosineChart]
  have he : (fun θ => cosineOscillator Λ θ * circleResidualAmplitude f θ) =
      (Ioc (-Real.pi) Real.pi).indicator F := by
    funext θ
    by_cases ht : θ ∈ Ioo (-Real.pi) Real.pi
    · have ht' : θ ∈ Ioc (-Real.pi) Real.pi := ⟨ht.1,ht.2.le⟩
      simp only [circleResidualAmplitude,compactCircleResidual,indicator_of_mem ht,
        indicator_of_mem ht',F]
      ring
    · by_cases ht' : θ ∈ Ioc (-Real.pi) Real.pi
      · have he : θ = Real.pi := by
          simp only [mem_Ioo,not_and_or,not_lt] at ht
          rcases ht with ht | ht <;> linarith [ht'.1,ht'.2]
        subst θ
        simp [circleResidualAmplitude,compactCircleResidual,F,hπ,ht']
      · simp [circleResidualAmplitude,compactCircleResidual,ht,ht']
  rw [he,integral_indicator measurableSet_Ioc]
  exact intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)

 theorem full_circle_decomposition (Λ : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hp : Function.Periodic f (2*Real.pi)) :
    (∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ * f θ) =
      localizedCircleIntegral Λ f + localizedCircleIntegral (-Λ) (fun θ => f (θ+Real.pi)) +
        ∫ θ : ℝ, cosineOscillator Λ θ * circleResidualAmplitude f θ := by
  let F₀ : ℝ → ℂ := fun θ => cosineOscillator Λ θ *
    (stationaryCutoff (stationarySineChart θ):ℂ)*f θ
  let Fπ : ℝ → ℂ := fun θ => cosineOscillator Λ θ *
    (stationaryCutoff (stationaryCosineChart θ):ℂ)*f θ
  let Fr : ℝ → ℂ := fun θ => cosineOscillator Λ θ * (circleStationaryResidual θ:ℂ)*f θ
  have hE := cosineOscillator_continuous Λ
  have hcs : Continuous stationarySineChart := by unfold stationarySineChart; fun_prop
  have hcc : Continuous stationaryCosineChart := by unfold stationaryCosineChart; fun_prop
  have h₀ : Continuous F₀ := (hE.mul (Complex.continuous_ofReal.comp (stationaryCutoff.continuous.comp hcs))).mul hf
  have hπ : Continuous Fπ := (hE.mul (Complex.continuous_ofReal.comp (stationaryCutoff.continuous.comp hcc))).mul hf
  have hr : Continuous Fr := (hE.mul (Complex.continuous_ofReal.comp circleStationaryResidual_contDiff.continuous)).mul hf
  have he : (fun θ => cosineOscillator Λ θ*f θ) = fun θ => (F₀ θ+Fπ θ)+Fr θ := by
    funext θ
    dsimp [F₀,Fπ,Fr,circleStationaryResidual]
    push_cast
    ring
  have hi₁ := intervalIntegral.integral_add (μ := volume) ((h₀.add hπ).intervalIntegrable (-Real.pi) Real.pi)
    (hr.intervalIntegrable (-Real.pi) Real.pi)
  have hi₀ := intervalIntegral.integral_add (μ := volume) (h₀.intervalIntegrable (-Real.pi) Real.pi)
    (hπ.intervalIntegrable (-Real.pi) Real.pi)
  simp only [Pi.add_apply] at hi₁
  rw [he,hi₁,hi₀]

  rw [show (∫ θ in (-Real.pi)..Real.pi, F₀ θ) = localizedCircleIntegral Λ f from
    circlePositivePiece_localized Λ f,
    show (∫ θ in (-Real.pi)..Real.pi, Fπ θ) = localizedCircleIntegral (-Λ) (fun θ => f (θ+Real.pi)) from
    circle_negative_piece Λ hp,
    show (∫ θ in (-Real.pi)..Real.pi, Fr θ) = ∫ θ : ℝ, cosineOscillator Λ θ * circleResidualAmplitude f θ from
    circle_residual_integral Λ f]

end PlanarFalconer

end OAI
