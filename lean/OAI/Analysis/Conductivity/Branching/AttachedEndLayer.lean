import Mathlib
import OAI.Analysis.Conductivity.Branching.AttachedEndL2
import OAI.Analysis.Conductivity.Variational.PhysicalStripIntegral
import OAI.Analysis.Conductivity.Geometry.SmoothCollarRate

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma continuous_angular_memLp {q : (Fin 3 → ℝ) → ℝ} (hq : Continuous q)
    {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    MemLp (fun z : ℝ×UnitAddTorus (Fin 2) => q (sourceAngularCollar z.1 z.2)) 2
      ((volume.restrict (Ioc l r)).prod volume) := by
  obtain ⟨M,hM⟩ := (isCompact_sourceClosedCollarBand (le_refl (-(1:ℝ)/100))
    (le_refl ((1:ℝ)/100))).exists_bound_of_continuousOn hq.continuousOn
  apply MemLp.of_bound (hq.comp continuous_uncurry_sourceAngularCollar).aestronglyMeasurable M
  have ht : ∀ᵐ z : ℝ×UnitAddTorus (Fin 2)∂(volume.restrict (Ioc l r)).prod volume,z.1∈Ioc l r :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with z hz
  apply hM
  change sourceCollarTime (sourceAngularCollar z.1 z.2)∈Icc (-(1:ℝ)/100) (1/100)
  rw [sourceAngular_time ⟨hl.trans hz.1.le,hz.2.trans hr⟩]
  exact ⟨hl.trans hz.1.le,hz.2.trans hr⟩

lemma smooth_attachedEnd_fiber_rate_volume {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {a b t : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100)) (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (hpos : 0<a*(t-b)) (htrace : ∀ h,f.val 0 h=mFourierCoeff
      (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h) :
    (∫ θ,((attachedEndPoissonField s f a b 0 (sourceAngularCollar t θ)).re-
      q (sourceAngularCollar t θ))^2)≤(2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)*(t-b)^2 := by
  rw [unitTorus_volume_eq_normalized]
  exact smooth_attachedEnd_fiber_rate hs f hq hK hb ht hpos htrace g hg

lemma smooth_attachedEnd_band_rate {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {a b l r R d : ℝ} (ha : a≠0) (hR : 0≤R) (_ : 0≤d)
    (hb : b∈Icc (-(1:ℝ)/100) (1/100)) (hlr : l≤r)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hnear : ∀ t∈Icc l r,|t-b|≤d)
    (htrace : ∀ h,f.val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h) :
    (∫ y in sourceClosedCollarBand l r,((attachedEndPoissonField s f a b 0 y).re-q y)^2)≤
      sourceCollarVolumeConstant*(r-l)*((2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)*d^2) := by
  apply sourceClosedBand_sq_integral_le
    ((Complex.measurable_re.comp (measurable_attachedEndPoissonField s f a b 0)).sub hq.continuous.measurable)
    hlr hl hr
  · exact ((attachedEndPoissonField_angular_memLp s hs f ha hR hl hr hT 0).re.sub
      (continuous_angular_memLp hq.continuous hl hr)).integrable_sq
  have ht : ∀ᵐ t∂volume.restrict (Ioc l r),t≠b := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_eq_eq_singleton] using (measure_singleton b : volume ({b}:Set ℝ)=0)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ht] with t ht hne
  have htb : t-b≠0 := sub_ne_zero.mpr hne
  have hpos : 0<a*(t-b) := lt_of_le_of_ne (hT t ⟨ht.1.le,ht.2⟩).1 (Ne.symm (mul_ne_zero ha htb))
  apply (smooth_attachedEnd_fiber_rate_volume hs f hq hK hb ⟨hl.trans ht.1.le,ht.2.trans hr⟩
    hpos htrace g hg).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hnear t ⟨ht.1.le,ht.2⟩) 2

end ScalarConductivity

end

end OAI
