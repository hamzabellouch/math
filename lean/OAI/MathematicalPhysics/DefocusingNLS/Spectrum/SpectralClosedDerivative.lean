import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialDerivativeUpgrade

namespace OAI

/-! A continuous weak derivative provides a classical extension through a finite radial endpoint. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralRadialRepresentative_closed_extension (R a b : ℝ) (hR : 0 < R)
    (ha : 0 < a) (hbR : b ≤ R) (u : SpectralRadialEnergy R)
    (F : ℝ → ℂ) (hF : Continuous F)
    (hD : ∀ᵐ t, t ∈ Icc a b → spectralRadialDerivative R u t=F t) :
    ∃ U : ℝ → ℂ, (∀ x, HasDerivAt U (F x) x) ∧
      EqOn U (spectralRadialRepresentative R hR u) (Icc a b) := by
  let U := fun t => spectralRadialPointValue R hR a ha u+∫ s in a..t, F s
  refine ⟨U,fun x =>
    (intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable a x)
      hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt).const_add _,?_⟩
  intro x hx
  have he := spectralRadialPointValue_integral R a x hR ha hx.1 (hx.2.trans hbR) u
  have hi : (∫ s in a..x, spectralRadialDerivative R u s)=∫ s in a..x, F s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hD] with s hs hsx
    rw [uIoc_of_le hx.1] at hsx
    exact hs ⟨hsx.1.le,hsx.2.trans hx.2⟩
  rw [hi] at he
  rw [spectralRadialRepresentative,dite_eq_left (ha.trans_le hx.1)]
  exact (by simpa only [U,add_comm] using (sub_eq_iff_eq_add.mp he).symm)

end DefocusingNLS

end OAI
