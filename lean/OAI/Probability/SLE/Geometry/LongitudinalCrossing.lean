import OAI.Probability.SLE.Geometry.RectangleCrossing
import OAI.Probability.SLE.Gauge.PassageRetention

namespace OAI

/-! The last-rear/first-front portion of an arbitrary continuous past is a
longitudinal rectangle crossing. Together with RectangleCrossing this
proves the separation assertion used in the ribbon waypoint argument. -/

noncomputable section
open Set
open scoped Topology

namespace SLEExactGauge.RectangleCrossing

theorem last_rear_before_first_front
    (x : ℝ → ℝ) {T a b : ℝ} (hT : 0 < T) (hab : a < b)
    (hx : ContinuousOn x (Icc 0 T)) (hstart : x 0 < a) (hend : b < x T) :
    ∃ u v : ℝ, 0 ≤ u ∧ u < v ∧ v < T ∧ x u = a ∧ x v = b ∧
      ∀ t ∈ Icc u v, x t ∈ Icc a b := by
  obtain ⟨v, hv, hxv, hprior⟩ := PassageRetention.first_progress_crossing x hT hx
    (hstart.trans hab) hend
  let K := Icc (0 : ℝ) v ∩ x ⁻¹' {a}
  have hKc : IsClosed K := (hx.mono (Icc_subset_Icc_right hv.2.le)).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_singleton
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset hKc inter_subset_left
  have hKn : K.Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hv.1.le
      (hx.mono (Icc_subset_Icc_right hv.2.le))
      (show a ∈ Icc (x 0) (x v) by rw [hxv]; exact ⟨hstart.le, hab.le⟩)
    exact ⟨t, ht, he⟩
  obtain ⟨u, hu, hmax⟩ := hK.exists_isGreatest hKn
  have hxu : x u = a := hu.2
  have huv : u < v := lt_of_le_of_ne hu.1.2 (by
    intro he
    have hh := he ▸ hxu
    rw [hxv] at hh
    exact (ne_of_gt hab) hh)
  refine ⟨u, v, hu.1.1, huv, hv.2, hxu, hxv, ?_⟩
  intro t ht
  refine ⟨?_, ?_⟩
  · by_contra hn
    have htx : x t < a := lt_of_not_ge hn
    obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc ht.2
      (hx.mono (Icc_subset_Icc (hu.1.1.trans ht.1) hv.2.le))
      (show a ∈ Icc (x t) (x v) by rw [hxv]; exact ⟨htx.le, hab.le⟩)
    have hsK : s ∈ K := ⟨⟨(hu.1.1.trans ht.1).trans hs.1, hs.2⟩, hxs⟩
    have hsu : s ≤ u := hmax hsK
    have htu : t = u := le_antisymm (hs.1.trans hsu) ht.1
    rw [htu, hxu] at htx
    exact (lt_irrefl a) htx
  · by_cases htv : t = v
    · rw [htv, hxv]
    · exact (hprior t ⟨hu.1.1.trans ht.1, lt_of_le_of_ne ht.2 htv⟩).le

def intervalParam (u v t : ℝ) : ℝ := u + (v - u) * t

theorem intervalParam_mem {u v t : ℝ} (huv : u ≤ v) (ht : t ∈ Icc (0 : ℝ) 1) :
    intervalParam u v t ∈ Icc u v := by
  have hp := mul_nonneg (sub_nonneg.mpr huv) ht.1
  have hq := mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr huv)
  dsimp [intervalParam]
  constructor <;> linarith

/-- The continuous past need not be simple. Its transverse separation
comes from a compact crossing portion, whose endpoints are selected in
the prescribed last-rear/first-front order. -/
theorem transverse_crossing_hits_past
    (p q : ℝ → ℂ) {T a b c d : ℝ} (hT : 0 < T) (hab : a < b) (hcd : c < d)
    (hp : ContinuousOn p (Icc 0 T)) (hq : ContinuousOn q (Icc 0 1))
    (hp0 : (p 0).re < a) (hpT : b < (p T).re)
    (hpim : ∀ t ∈ Icc (0 : ℝ) T, (p t).im ∈ Icc c d)
    (hqr : ∀ t ∈ Icc (0 : ℝ) 1, (q t).re ∈ Icc a b ∧ (q t).im ∈ Icc c d)
    (hq0 : (q 0).im = c) (hq1 : (q 1).im = d) :
    ∃ s ∈ Icc (0 : ℝ) T, ∃ t ∈ Icc (0 : ℝ) 1, p s = q t := by
  have hx : ContinuousOn (fun t => (p t).re) (Icc 0 T) :=
    Complex.continuous_re.comp_continuousOn hp
  obtain ⟨u, v, hu, huv, hvT, hpu, hpv, hrect⟩ :=
    last_rear_before_first_front (fun t => (p t).re) hT hab hx hp0 hpT
  have hmap : MapsTo (intervalParam u v) (Icc (0 : ℝ) 1) (Icc 0 T) := by
    intro t ht
    exact (Icc_subset_Icc hu hvT.le) (intervalParam_mem huv.le ht)
  have hparam : Continuous (intervalParam u v) := by unfold intervalParam; fun_prop
  have hcomp : ContinuousOn (fun t => p (intervalParam u v t)) (Icc 0 1) :=
    hp.comp hparam.continuousOn hmap
  obtain ⟨s, hs, t, ht, he⟩ := paths_intersect_rectangle
    (fun t => p (intervalParam u v t)) q a b c d hab hcd hcomp hq
    (fun t ht => ⟨hrect _ (intervalParam_mem huv.le ht), hpim _ (hmap ht)⟩) hqr
    (by simpa [intervalParam] using hpu) (by simpa [intervalParam] using hpv) hq0 hq1
  exact ⟨intervalParam u v s, hmap hs, t, ht, he⟩

end SLEExactGauge.RectangleCrossing

end

end OAI
