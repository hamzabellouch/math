import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCorePolarEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoreFreeIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhaseConvergence

namespace OAI

/-! The origin-normalized polar limit is the prescribed complex free IVP, with its phase. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_core_polar_identification (R l b : ℝ) (hl : (3 : ℝ) ≤ l) (hlR : l < R)
    (hRu : R ≤ (10/3 : ℝ)) (hwidth : R-l ≤ (1/1000 : ℝ))
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (A D : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hAP : ∀ r ∈ Icc 0 R, 0 < A r)
    (hcore : EqOn A (fun _ => 1) (Icc 0 l)) (hDl : D l=0)
    (hAD : ∀ r ∈ Ioo l R, HasDerivAt A (D r) r)
    (hDE : ∀ r ∈ Ioo l R, HasDerivAt D
      (-11/r*D r-radialAmplitudePotential 6 b A r*A r) r)
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hFI : ∀ r ∈ Icc l R, F r=1+∫ t in l..r, G t)
    (hGI : ∀ r ∈ Icc l R, G r=∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t) :
    EqOn (radialPolar A (radialPhase 6 (radialClampedAmplitude R A))) F (Icc l R) ∧
    EqOn (radialPolarSlope A D (radialPhaseSpeed 6 A)
      (radialPhase 6 (radialClampedAmplitude R A))) G (Icc l R) := by
  let B := radialClampedAmplitude R A
  let φ := radialPhase 6 B
  let v := fun r => (radialVelocity 6 B r-r/2)/2
  let F₀ := radialPolar B φ
  let G₀ := radialPolarSlope B D v φ
  obtain ⟨hF₀,hG₀,hF₀l,hG₀l,hder,_⟩ := radial_core_polar_free R l b (by linarith) hlR
    A D hA hD hAP hcore hDl hAD hDE
  obtain ⟨hF₀I,hG₀I⟩ := radial_free_integral_of_derivatives b l R (by linarith)
    F₀ G₀ hF₀ hG₀ hF₀l hG₀l hder
  have hx₀ := radial_free_components_state b l R (by linarith) F₀ G₀ hF₀ hG₀ 1 0
    hF₀I (by simpa only [zero_add] using hG₀I)
  have hx := radial_free_components_state b l R (by linarith) F G hFc hGc 1 0
    hFI (by simpa only [zero_add] using hGI)
  have he := radial_free_integral_unique b l R hb hl hRu hlR.le hwidth
    (fun r => (F₀ r,G₀ r)) (fun r => (F r,G r)) (hF₀.prodMk hG₀) (hFc.prodMk hGc) hx₀ hx
  constructor
  · intro r hr
    have hh := congrArg Prod.fst (he hr)
    change radialPolar B φ r=F r at hh
    simpa only [radialPolar,B,radialClampedAmplitude_eq R A r ⟨by linarith [hr.1],hr.2⟩] using hh
  · intro r hr
    have hh := congrArg Prod.snd (he hr)
    change radialPolarSlope B D v φ r=G r at hh
    have hrI : r ∈ Icc 0 R := ⟨by linarith [hr.1],hr.2⟩
    simpa only [radialPolarSlope,B,v,radialClampedAmplitude_eq R A r hrI,
      radialVelocity_clamped_eq 6 R A r hrI,radialPhaseSpeed] using hh

end DefocusingNLS

end OAI
