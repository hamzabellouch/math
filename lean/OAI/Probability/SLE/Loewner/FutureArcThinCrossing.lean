import OAI.Probability.SLE.Loewner.InverseThinCollapse
import OAI.Probability.SLE.Loewner.FutureSlitHeight
import OAI.Probability.SLE.Loewner.MappedFutureRange

namespace OAI

/-! A real crossing of the actual mapped future supplies the small
inverse values required by the Dirichlet-energy criterion. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology

namespace SLEExactGauge

theorem mappedFutureArc_thin_crossing (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) {x ε : ℝ} (c : ℂ)
    (hx : x∈Ioo (initialDrivingValue p hi h0 hH s (hst.trans ht))
        (initialForwardChart p hi h0 hH s (p t)).re ∨
      x∈Ioo (initialForwardChart p hi h0 hH s (p t)).re
        (initialDrivingValue p hi h0 hH s (hst.trans ht)))
    (hp : ∀ v∈Ioc s t, ‖p v-c‖≤ε) :
    ∃ y∈Ioc 0 (Real.sqrt (2*(initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s))),
      ‖initialInverseChart p hi h0 hH s ((x:ℂ)+(y:ℂ)*I)-c‖≤ε := by
  let q := mappedFutureArc p hi h0 hH hst ht
  have hq0 : (q 0).re=initialDrivingValue p hi h0 hH s (hst.trans ht) := by
    simp [q]
  have hq1 : q 1=initialForwardChart p hi h0 hH s (p t) := by
    rw [mappedFutureArc_segment p hi h0 hH hst ht one_ne_zero,slitSegmentParameter_one]
  have hcont : ContinuousOn (fun u => (q u).re) (Icc (0:unitInterval) 1) :=
    (Complex.continuous_re.comp q.continuous).continuousOn
  have hex : ∃ u∈Icc (0:unitInterval) 1, (q u).re=x := by
    rcases hx with hx | hx
    · apply intermediate_value_Icc (show (0:unitInterval)≤1 from zero_le_one) hcont
      simpa only [hq0,hq1] using ⟨hx.1.le,hx.2.le⟩
    · apply intermediate_value_Icc' (show (0:unitInterval)≤1 from zero_le_one) hcont
      simpa only [hq0,hq1] using ⟨hx.1.le,hx.2.le⟩
  obtain ⟨u,_,hux⟩ := hex
  have hu : u≠0 := by
    intro he
    subst u
    rw [hq0] at hux
    rcases hx with hx | hx <;> linarith [hx.1,hx.2]
  have hpos : 0<(q u).im := mappedFutureArc_upper p hi h0 hH hst ht hu
  have him : (centeredFutureArc p hi h0 hH hst ht u).im=(q u).im := by
    change (q u-(_ : ℂ)).im=(q u).im
    simp only [sub_im,ofReal_im,sub_zero]
  have hsq := centeredFutureArc_height_sq_le p hi h0 hH hst ht u
  rw [him] at hsq
  have hcap : 0≤2*(initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr (initialCapacity_monotone p hi h0 hH hst.le))
  have hheight : (q u).im≤Real.sqrt (2*(initialCapacity p hi h0 hH t-initialCapacity p hi h0 hH s)) :=
    (Real.le_sqrt hpos.le hcap).mpr hsq
  have hcoord : (x:ℂ)+((q u).im:ℂ)*I=q u := by
    apply Complex.ext <;> simp [hux]
  refine ⟨(q u).im,⟨hpos,hheight⟩,?_⟩
  rw [hcoord,mappedFutureArc_segment p hi h0 hH hst ht hu,
    initialInverse_forward_at p hi h0 hH s
      (point_after_prefix_mem_domain p hi hH (slitSegmentParameter_gt hst hu))]
  exact hp _ ⟨slitSegmentParameter_gt hst hu,slitSegmentParameter_le s t hst.le u⟩

end SLEExactGauge

end

end OAI
