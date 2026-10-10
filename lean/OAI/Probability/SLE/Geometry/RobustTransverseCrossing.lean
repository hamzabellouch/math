import OAI.Probability.SLE.Geometry.LongitudinalCrossing

namespace OAI

/-! Rectangle separation remains valid for a perturbed transverse route:
its ends may lie beyond the narrow core, with no regularity of the past. -/

noncomputable section
open Set Metric
open scoped Topology

namespace SLEExactGauge.RectangleCrossing

theorem transverse_crossing_beyond_edges_hits_past
    (p q : ℝ → ℂ) {T a b c d : ℝ} (hT : 0 < T) (hab : a < b) (hcd : c < d)
    (hp : ContinuousOn p (Icc 0 T)) (hq : ContinuousOn q (Icc 0 1))
    (hp0 : (p 0).re < a) (hpT : b < (p T).re)
    (hpim : ∀ t ∈ Icc (0 : ℝ) T, (p t).im ∈ Icc c d)
    (hqr : ∀ t ∈ Icc (0 : ℝ) 1, (q t).re ∈ Icc a b)
    (hq0 : (q 0).im < c) (hq1 : d < (q 1).im) :
    ∃ s ∈ Icc (0 : ℝ) T, ∃ t ∈ Icc (0 : ℝ) 1, p s = q t := by
  obtain ⟨u, v, hu, huv, hv, hqu, hqv, hrect⟩ := last_rear_before_first_front
    (fun t => (q t).im) (by norm_num : (0 : ℝ) < 1) hcd
    (Complex.continuous_im.comp_continuousOn hq) hq0 hq1
  have hmap : MapsTo (intervalParam u v) (Icc (0 : ℝ) 1) (Icc 0 1) :=
    fun t ht => (Icc_subset_Icc hu hv.le) (intervalParam_mem huv.le ht)
  have hparam : Continuous (intervalParam u v) := by unfold intervalParam; fun_prop
  obtain ⟨s, hs, t, ht, he⟩ := transverse_crossing_hits_past p
    (fun t => q (intervalParam u v t)) hT hab hcd hp
    (hq.comp hparam.continuousOn hmap) hp0 hpT hpim
    (fun t ht => ⟨hqr _ (hmap ht), hrect _ (intervalParam_mem huv.le ht)⟩)
    (by simpa [intervalParam] using hqu) (by simpa [intervalParam] using hqv)
  exact ⟨s, hs, intervalParam u v t, hmap ht, he⟩

def transverseTemplate (k t : ℝ) : ℂ :=
  (((k - 1 / 2 : ℝ) : ℂ)) + (((t - 1 / 2 : ℝ) : ℂ)) * Complex.I

/-- A fixed coordinate tube around the transverse segment forces a hit
of any continuous past crossing the ribbon's narrow core. -/
theorem near_transverse_template_hits_past
    (p q : ℝ → ℂ) {T k ε δ : ℝ} (hT : 0 < T) (hk : 1 ≤ k)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 8) (hδ : δ ≤ 1 / 8)
    (hp : ContinuousOn p (Icc 0 T)) (hq : ContinuousOn q (Icc 0 1))
    (hp0 : (p 0).re = 0) (hpT : (p T).re = k)
    (hpim : ∀ t ∈ Icc (0 : ℝ) T, |(p t).im| ≤ ε)
    (hnear : ∀ t ∈ Icc (0 : ℝ) 1, dist (q t) (transverseTemplate k t) < δ) :
    ∃ s ∈ Icc (0 : ℝ) T, ∃ t ∈ Icc (0 : ℝ) 1, p s = q t := by
  have hre t (ht : t ∈ Icc (0 : ℝ) 1) : |(q t).re - (k - 1 / 2)| < δ := by
    have hh := (Complex.abs_re_le_norm (q t - transverseTemplate k t)).trans_lt
      (show ‖q t - transverseTemplate k t‖ < δ by simpa only [dist_eq_norm] using hnear t ht)
    simpa [transverseTemplate] using hh
  have him t (ht : t ∈ Icc (0 : ℝ) 1) : |(q t).im - (t - 1 / 2)| < δ := by
    have hh := (Complex.abs_im_le_norm (q t - transverseTemplate k t)).trans_lt
      (show ‖q t - transverseTemplate k t‖ < δ by simpa only [dist_eq_norm] using hnear t ht)
    simpa [transverseTemplate] using hh
  apply transverse_crossing_beyond_edges_hits_past p q hT
    (by norm_num : k - 3 / 4 < k - 1 / 4) (by linarith : -ε < ε) hp hq
    (by rw [hp0]; linarith) (by rw [hpT]; linarith)
    (fun t ht => abs_le.mp (hpim t ht))
  · intro t ht
    have hh := abs_lt.mp (hre t ht)
    constructor <;> linarith
  · have hh := abs_lt.mp (him 0 (by norm_num))
    linarith
  · have hh := abs_lt.mp (him 1 (by norm_num))
    linarith

end SLEExactGauge.RectangleCrossing

end

end OAI
