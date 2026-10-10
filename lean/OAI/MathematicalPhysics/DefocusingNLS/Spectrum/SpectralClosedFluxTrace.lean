import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedFluxPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace OAI

/-! Recover the flux trace from the weak equation, after its continuous extension. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralClosedFlux_ae_primitive (a b : ℝ) (hab : a < b) (F C G : ℝ → ℂ)
    (hG : ContinuousOn G (Icc a b))
    (hC : ∀ x ∈ Ioo a b, HasDerivAt C (G x) x)
    (hFC : ∀ᵐ x, x ∈ Ioo a b → F x=C x) :
    ∃ P : ℝ → ℂ, Continuous P ∧
      (∀ x ∈ Icc a b, HasDerivAt P (G x) x) ∧
      EqOn C P (Ioo a b) ∧ (∀ᵐ x, x ∈ Icc a b → F x=P x) := by
  obtain ⟨P,hP,hd,he⟩ := spectralClosedFlux_primitive a b hab C G hG hC
  refine ⟨P,hP,hd,he,?_⟩
  have hna : ∀ᵐ x : ℝ, x ≠ a := by
    simpa using (Set.countable_singleton a).ae_notMem (volume : Measure ℝ)
  have hnb : ∀ᵐ x : ℝ, x ≠ b := by
    simpa using (Set.countable_singleton b).ae_notMem (volume : Measure ℝ)
  filter_upwards [hFC,hna,hnb] with x hx hxa hxb hxab
  have hm : x ∈ Ioo a b := ⟨lt_of_le_of_ne hxab.1 hxa.symm,lt_of_le_of_ne hxab.2 hxb⟩
  exact (hx hm).trans (he hm)

theorem spectralClosedFlux_trace (a b : ℝ) (hab : a < b) (F G₀ P G : ℝ → ℂ)
    (hP : Continuous P) (hG : ContinuousOn G (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivAt P (G x) x)
    (hF : ∀ᵐ x, x ∈ Icc a b → F x=P x)
    (hG₀ : ∀ᵐ x, x ∈ Icc a b → G₀ x=G x)
    (f : 𝓢(ℝ,ℂ)) (hfa : f a=0) (hfb : f b=1) (β : ℂ)
    (hw : (∫ x in a..b, star (deriv f x)*F x)=
      β-(∫ x in a..b, star (f x)*G₀ x)) : P b=β := by
  have hFint : (∫ x in a..b, star (deriv f x)*F x)=
      ∫ x in a..b, star (deriv f x)*P x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hF] with x hx hxab
    rw [uIoc_of_le hab.le] at hxab
    rw [hx ⟨hxab.1.le,hxab.2⟩]
  have hGint : (∫ x in a..b, star (f x)*G₀ x)=
      ∫ x in a..b, star (f x)*G x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hG₀] with x hx hxab
    rw [uIoc_of_le hab.le] at hxab
    rw [hx ⟨hxab.1.le,hxab.2⟩]
  have hs : uIcc a b=Icc a b := uIcc_of_le hab.le
  have hi₁ : IntervalIntegrable (fun x => star (deriv f x)*P x) volume a b :=
    ((f.smooth 1).continuous_deriv_one.star.mul hP).intervalIntegrable a b
  have hi₂ : IntervalIntegrable (fun x => star (f x)*G x) volume a b :=
    ((f.continuous.star.continuousOn).mul hG).intervalIntegrable_of_Icc hab.le
  have hp := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ => (f.differentiableAt (x := x)).hasDerivAt.star)
    (fun x hx => hd x (by rwa [hs] at hx))
    ((f.smooth 1).continuous_deriv_one.star.intervalIntegrable (μ := volume) a b)
    (hG.intervalIntegrable_of_Icc (μ := volume) hab.le)
  rw [intervalIntegral.integral_add hi₁ hi₂,hfa,hfb,star_zero,star_one,zero_mul,one_mul,sub_zero] at hp
  rw [hFint,hGint] at hw
  linear_combination hw-hp

end DefocusingNLS

end OAI
