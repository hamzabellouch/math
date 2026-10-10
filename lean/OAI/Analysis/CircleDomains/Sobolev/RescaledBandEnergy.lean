import OAI.Analysis.CircleDomains.Selection.RescaledBandWitness
import OAI.Analysis.CircleDomains.Sobolev.SobolevCapacityMass
import OAI.Analysis.CircleDomains.Sobolev.AffineLIntegral

namespace OAI

/-! Integrating the actual band-test energy and returning to physical
coordinates gives the local energy payment required by graph covers. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma rescaled_band_set (u : EuclideanPlane → ℝ) (a : EuclideanPlane) (t : ℝ)
    {s : ℝ} (hs : 0 < s) (x : EuclideanPlane) :
    (‖a+s • x-a‖ ≤ 4*s ∧ |u (a+s • x)-t| ≤ 2*s) ↔
      (‖x‖ ≤ 4 ∧ |u (a+s • x)-t| ≤ 2*s) := by
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  constructor <;> intro h
  · exact ⟨by nlinarith [h.1],h.2⟩
  · exact ⟨by nlinarith [h.1],h.2⟩

lemma rescaled_band_energy_payment {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C)
    (hηd : ∀ y, ‖fderiv ℝ spatialCapacityBump y‖ ≤ C) :
    let w := fun x => spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s)
    let Q := rescaledBandWitness hu W hsu a t hs hC
    ENNReal.ofReal (s^2) *
      (ENNReal.ofReal (∫ p, (w (euclideanPlaneCoordinates.symm p))^2) +
        coordinateSobolevEnergy Q.weakGrad univ) ≤
      ENNReal.ofReal (1+8*C^2) *
        ∫⁻ y in {y : EuclideanPlane | ‖y-a‖ ≤ 4*s ∧ |u y-t| ≤ 2*s},
          ENNReal.ofReal (1+(|W.weakGrad y 0|+|W.weakGrad y 1|)^2) := by
  dsimp only
  let w := fun x => spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s)
  let Q := rescaledBandWitness hu W hsu a t hs hC
  have hw : Continuous w := spatialCapacityBump.continuous.mul
    (scalarCapacityBump.continuous.comp
      ((hu.comp (planarAffineHomeomorph a s hs.ne').continuous).sub continuous_const |>.div_const s))
  have hLp : MemLp (fun p => w (euclideanPlaneCoordinates.symm p)) 2 volume :=
    (show MemLp w 2 volume by simpa only [Measure.restrict_univ] using Q.memLp).comp_measurePreserving
      euclideanPlaneCoordinates_symm_measurePreserving
  rw [sobolev_capacity_mass hw hLp Q.weakGrad]
  let S := {y : EuclideanPlane | ‖y-a‖ ≤ 4*s ∧ |u y-t| ≤ 2*s}
  have hS : MeasurableSet S :=
    (isClosed_le (continuous_id.sub continuous_const |>.norm) continuous_const).measurableSet.inter
      (isClosed_le ((hu.sub continuous_const).abs) continuous_const).measurableSet
  let g := fun y => ENNReal.ofReal (1+8*C^2) *
    ENNReal.ofReal (1+(|W.weakGrad y 0|+|W.weakGrad y 1|)^2)
  have hbound (x : EuclideanPlane) :
      ENNReal.ofReal ((w x)^2+(|Q.weakGrad x 0|+|Q.weakGrad x 1|)^2) ≤
        S.indicator g (a+s • x) := by
    have he := ENNReal.ofReal_le_ofReal (rescaledBandWitness_energy hu W hsu a t hs hC0 hC hηd x)
    by_cases hx : x ∈ {y : EuclideanPlane | ‖y‖ ≤ 4 ∧ |u (a+s • y)-t| ≤ 2*s}
    · have hy : a+s • x ∈ S := (rescaled_band_set u a t hs x).mpr hx
      rw [indicator_of_mem hy]
      simp only [indicator_of_mem hx] at he
      rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 1+8*C^2 by positivity)] at he
      exact he
    · have hy : a+s • x ∉ S := fun h => hx ((rescaled_band_set u a t hs x).mp h)
      rw [indicator_of_notMem hy]
      simpa only [indicator_of_notMem hx, ENNReal.ofReal_zero, w, Q] using he
  calc
    _ ≤ ENNReal.ofReal (s^2) * ∫⁻ x, S.indicator g (a+s • x) :=
      mul_le_mul' le_rfl (lintegral_mono hbound)
    _ = ∫⁻ y, S.indicator g y := scaled_lintegral_planarAffine a hs _
    _ = _ := by
      rw [lintegral_indicator hS, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end CircleDomainRigidity

end

end OAI
