import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedFluxTrace

namespace OAI

/-! A test supported away from the core reads the outer trace of a weak flux. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralIntegral_lowerCutoff (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (F : ℝ → ℂ) (hF : IntervalIntegrable F volume 0 b) (hz : ∀ x ≤ a, F x=0) :
    (∫ x in (0 : ℝ)..b, F x)=∫ x in a..b, F x := by
  have hm : a ∈ uIcc (0 : ℝ) b := by rw [uIcc_of_le (ha.trans hab)]; exact ⟨ha,hab⟩
  obtain ⟨h₁,h₂⟩ := (IntervalIntegrable.trans_iff hm).mp hF
  have hzero : (∫ x in (0 : ℝ)..a, F x)=0 := by
    apply intervalIntegral.integral_zero_ae
    exact Filter.Eventually.of_forall (fun x hx => hz x ((uIoc_of_le ha ▸ hx).2))
  have he := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  simpa only [hzero,zero_add] using he.symm

theorem spectralCutoffFlux_trace (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (F G₀ P G : ℝ → ℂ) (hP : Continuous P) (hG : ContinuousOn G (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivAt P (G x) x)
    (hF : ∀ᵐ x, x ∈ Icc a b → F x=P x)
    (hG₀ : ∀ᵐ x, x ∈ Icc a b → G₀ x=G x)
    (f : 𝓢(ℝ,ℂ)) (hfb : f b=1) (hf : ∀ x ≤ a, f x=0)
    (hdf : ∀ x ≤ a, deriv f x=0) (β : ℂ)
    (hw : (∫ x in (0 : ℝ)..b, star (deriv f x)*F x)=
      β-(∫ x in (0 : ℝ)..b, star (f x)*G₀ x)) : P b=β := by
  let clamp := fun x : ℝ => max a (min b x)
  have hc (x : ℝ) : clamp x ∈ Icc a b :=
    ⟨le_max_left _ _,max_le hab.le (min_le_left _ _)⟩
  have hfix (x : ℝ) (hx : x ∈ Icc a b) : clamp x=x := by
    dsimp only [clamp]
    rw [min_eq_right hx.2,max_eq_right hx.1]
  let G₁ := fun x => G (clamp x)
  have hG₁ : Continuous G₁ := hG.comp_continuous (by fun_prop) hc
  have heF : (∫ x in (0 : ℝ)..b, star (deriv f x)*F x)=
      ∫ x in (0 : ℝ)..b, star (deriv f x)*P x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hF] with x hx hxb
    by_cases hxa : x ≤ a
    · simp only [hdf x hxa,star_zero,zero_mul]
    · rw [uIoc_of_le (ha.trans hab.le)] at hxb
      rw [hx ⟨(lt_of_not_ge hxa).le,hxb.2⟩]
  have heG : (∫ x in (0 : ℝ)..b, star (f x)*G₀ x)=
      ∫ x in (0 : ℝ)..b, star (f x)*G₁ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hG₀] with x hx hxb
    by_cases hxa : x ≤ a
    · simp only [hf x hxa,star_zero,zero_mul]
    · rw [uIoc_of_le (ha.trans hab.le)] at hxb
      have hm : x ∈ Icc a b := ⟨(lt_of_not_ge hxa).le,hxb.2⟩
      rw [hx hm]
      simp only [G₁,hfix x hm]
  rw [heF,heG] at hw
  rw [spectralIntegral_lowerCutoff a b ha hab.le (fun x => star (deriv f x)*P x)
    (((f.smooth 1).continuous_deriv_one.star.mul hP).intervalIntegrable 0 b)
    (fun x hx => by simp only [hdf x hx,star_zero,zero_mul]),
    spectralIntegral_lowerCutoff a b ha hab.le (fun x => star (f x)*G₁ x)
    ((f.continuous.star.mul hG₁).intervalIntegrable 0 b)
    (fun x hx => by simp only [hf x hx,star_zero,zero_mul])] at hw
  apply spectralClosedFlux_trace a b hab P G₁ P G hP hG hd
    (Filter.Eventually.of_forall (fun _ _ => rfl))
    (Filter.Eventually.of_forall (fun x hx => congrArg G (hfix x hx)))
    f (hf a le_rfl) hfb β hw

end DefocusingNLS

end OAI
