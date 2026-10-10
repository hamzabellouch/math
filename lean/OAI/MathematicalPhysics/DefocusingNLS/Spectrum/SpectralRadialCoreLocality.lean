import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialPrimitiveIntegral

namespace OAI

/-! A radial H¹ vector that vanishes in the core also has zero weak derivative there. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralRadialCore_point_zero_of_le (R l r : ℝ) (hR : 0 < R)
    (hr : 0 < r) (hrl : r ≤ l) (hlR : l ≤ R) (u : SpectralRadialEnergy R)
    (hu : (fun s => spectralRadialValue R u s) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0) :
    spectralRadialPointValue R hR r hr u=0 := by
  apply spectralRadialCore_point_zero R r hR hr (hrl.trans hlR) u
  exact (Measure.absolutelyContinuous_of_le
    (Measure.restrict_mono (Iic_subset_Iic.mpr hrl) le_rfl)).ae_le hu

theorem spectralRadialCore_derivative_local (R l δ : ℝ) (hR : 0 < R)
    (hδ : 0 < δ) (hδl : δ < l) (hlR : l ≤ R) (u : SpectralRadialEnergy R)
    (hu : (fun s => spectralRadialValue R u s) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0) :
    ∀ᵐ r ∂volume, r ∈ Ioo δ l → spectralRadialDerivative R u r=0 := by
  have hi := spectralRadialL2_intervalIntegrable R δ l hδ hδl.le hlR
    (spectralRadialDerivative R u)
  have he (r : ℝ) (hr : r ∈ Icc δ l) :
      (∫ s in δ..r, spectralRadialDerivative R u s)=0 := by
    rw [← spectralRadialPointValue_integral R δ r hR hδ hr.1 (hr.2.trans hlR),
      spectralRadialCore_point_zero_of_le R l r hR (hδ.trans_le hr.1) hr.2 hlR u hu,
      spectralRadialCore_point_zero_of_le R l δ hR hδ hδl.le hlR u hu,sub_self]
  filter_upwards [hi.ae_hasDerivAt_integral] with r hr hrl
  have hd := hr (by simpa only [uIcc_of_le hδl.le] using ⟨hrl.1.le,hrl.2.le⟩)
    δ (by simp [hδl.le])
  have hz : (fun r => ∫ s in δ..r, spectralRadialDerivative R u s) =ᶠ[𝓝 r]
      fun _ => (0 : ℂ) := by
    filter_upwards [Ioo_mem_nhds hrl.1 hrl.2] with s hs
    exact he s ⟨hs.1.le,hs.2.le⟩
  exact hd.unique ((hasDerivAt_const r (0 : ℂ)).congr_of_eventuallyEq hz)

theorem spectralRadialCore_derivative_zero (R l : ℝ) (hR : 0 < R)
    (hlR : l ≤ R) (u : SpectralRadialEnergy R)
    (hu : (fun s => spectralRadialValue R u s) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0) :
    (fun s => spectralRadialDerivative R u s) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0 := by
  have hall : ∀ᵐ r ∂volume, ∀ n : ℕ,
      1/((n : ℝ)+1) < r → r < l → spectralRadialDerivative R u r=0 := by
    apply ae_all_iff.mpr
    intro n
    have hn : 0 < 1/((n : ℝ)+1) := by positivity
    by_cases hnl : 1/((n : ℝ)+1) < l
    · filter_upwards [spectralRadialCore_derivative_local R l _ hR hn hnl hlR u hu]
        with r hr hn hrL
      exact hr ⟨hn,hrL⟩
    · exact Eventually.of_forall (fun r hn hrL => False.elim (hnl (hn.trans hrL)))
  have hac : radialPressureMeasure R ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous
  have hlne : ∀ᵐ r ∂radialPressureMeasure R, r ≠ l := by
    simp only [ae_iff]
    simpa using spectralRadialMeasure_singleton R l
  change ∀ᵐ r ∂(radialPressureMeasure R).restrict (Iic l), spectralRadialDerivative R u r=0
  rw [ae_restrict_iff' measurableSet_Iic]
  filter_upwards [hac.ae_le hall,radialPressureMeasure_ae_positive R,hlne] with r hr hp hn hrl
  obtain ⟨n,hN⟩ := exists_nat_one_div_lt hp.1
  exact hr n hN (lt_of_le_of_ne hrl hn)

end DefocusingNLS

end OAI
