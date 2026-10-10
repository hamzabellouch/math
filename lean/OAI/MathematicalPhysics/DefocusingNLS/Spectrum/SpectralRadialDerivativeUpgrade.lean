import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialPrimitiveIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakFluxPrimitive

namespace OAI

/-! Recover a classical derivative from the continuous representative of the weak radial derivative. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralRadialRepresentative_hasDerivAt (R a b : ℝ) (hR : 0 < R)
    (ha : 0 < a) (hbR : b ≤ R) (u : SpectralRadialEnergy R)
    (F : ℝ → ℂ) (hF : Continuous F)
    (hD : ∀ᵐ t, t ∈ Icc a b → spectralRadialDerivative R u t=F t)
    (x : ℝ) (hx : x ∈ Ioo a b) :
    HasDerivAt (spectralRadialRepresentative R hR u) (F x) x := by
  let P := fun t => spectralRadialPointValue R hR a ha u + ∫ s in a..t, F s
  have hd : HasDerivAt P (F x) x :=
    (intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable a x)
      hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt).const_add _
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  have he := spectralRadialPointValue_integral R a t hR ha ht.1.le
    (ht.2.le.trans hbR) u
  have hi : (∫ s in a..t, spectralRadialDerivative R u s)=∫ s in a..t, F s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hD] with s hs hst
    rw [uIoc_of_le ht.1.le] at hst
    exact hs ⟨hst.1.le,hst.2.trans ht.2.le⟩
  rw [hi] at he
  rw [spectralRadialRepresentative,dite_eq_left (ha.trans ht.1)]
  have heq := sub_eq_iff_eq_add.mp he
  simpa only [P,add_comm] using heq

end DefocusingNLS

end OAI
