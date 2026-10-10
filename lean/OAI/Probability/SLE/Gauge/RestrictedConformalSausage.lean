import OAI.Probability.SLE.Gauge.ConformalSausageTransfer
import OAI.Probability.SLE.Mass.StoppedConformalPassageMass

namespace OAI

/-! Area transport of the part of a stopped sausage in a prescribed
region. Agreement of the physical trace with the conformal image is only
needed at the nearby interior witnesses. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

theorem restricted_segment_sausage_conformal_transfer
    (κ : ℝ) (F F' : ℂ → ℂ) (γ η : ℝ≥0 → ℂ) (s t : ℝ≥0)
    (D K R : Set ℂ) (hD : MeasurableSet D) (hDK : D ⊆ K) (hK : Convex ℝ K)
    (hinj : InjOn F K) (hF : ∀ z ∈ K, HasDerivAt F (F' z) z)
    {c v ell : ℝ} (hc : 0 ≤ c) (hv : 0 < v) (hell : 0 < ell)
    (hlo : ∀ z ∈ D, c ≤ ‖F' z‖)
    (C : ℝ≥0) (hup : ∀ z ∈ K, ‖F' z‖₊ ≤ C)
    (hscale : (C : ℝ) * ell ≤ 1)
    (hnear : ∀ z ∈ D, ∀ y : ℂ, dist z y < ell * v → y ∈ K)
    (heq : ∀ u ∈ Icc s t, γ u ∈ K → η u = F (γ u))
    (himage : F '' D ⊆ R) :
    ENNReal.ofReal (c ^ 2 * ell ^ codimension κ) *
        segmentSausageCharge κ γ s t (ell * v) D ≤
      segmentSausageCharge κ η s t v R := by
  have hLip : LipschitzOnWith C F K :=
    hK.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hF z hz).hasDerivWithinAt) hup
  apply normalized_conformal_area_lower
    (hD.inter (source_sausage_isOpen γ s t (ell * v)).measurableSet)
    (hinj.mono (inter_subset_left.trans hDK))
    (fun z hz => hF z (hDK hz.1)) hc hv hell (fun z hz => hlo z hz.1)
  rintro _ ⟨z, ⟨hzD, u, hu, hd⟩, rfl⟩
  refine ⟨himage (mem_image_of_mem F hzD), u, hu, ?_⟩
  have huK : γ u ∈ K := hnear z hzD (γ u) hd
  rw [heq u hu huK]
  have hdist := hLip.dist_le_mul z (hDK hzD) (γ u) huK
  by_cases hC : C = 0
  · have hdist0 : dist (F z) (F (γ u)) ≤ 0 := by
      simpa only [hC, NNReal.coe_zero, zero_mul] using hdist
    exact hdist0.trans_lt hv
  · have hCp : 0 < (C : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hC)
    calc
      dist (F z) (F (γ u)) ≤ (C : ℝ) * dist z (γ u) := hdist
      _ < (C : ℝ) * (ell * v) := mul_lt_mul_of_pos_left hd hCp
      _ ≤ v := by nlinarith [mul_le_mul_of_nonneg_right hscale hv.le]

lemma conformal_transfer_coefficient
    (κ : ℝ) {c C a : ℝ} (hC : 0 < C) (ha : 0 < a) :
    (c * a) ^ 2 * (1 / (C * a)) ^ codimension κ =
      (c ^ 2 * (1 / C) ^ codimension κ) * a ^ dimension κ := by
  have he : (1 / (C * a)) = (1 / C) * (1 / a) := by ring
  rw [he, Real.mul_rpow (by positivity) (by positivity),
    Real.div_rpow zero_le_one ha.le, Real.one_rpow]
  calc
    _ = (c ^ 2 * (1 / C) ^ codimension κ) * (a ^ 2 / a ^ codimension κ) := by ring
    _ = _ := by
      congr 1
      rw [← Real.rpow_two, ← Real.rpow_sub ha]
      congr 1
      unfold codimension
      ring

end SLEExactGauge

end

end OAI
