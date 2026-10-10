import OAI.Probability.SLE.Geometry.BoundaryRadialDistance
import OAI.Probability.SLE.Loewner.SmoothRawTrace

namespace OAI

/-! A positive reverse solution that starts at the driver and satisfies
the local cone estimate ends at the exact raw trace. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem boundary_reverse_eq_trace_of_cone
    (b : Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L a : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L)
    (ha : 0 < a) (haT : a ≤ T) (hsmall : L^2*a ≤ 1)
    (q : ℝ → ℂ) (hqc : ContinuousOn q (Icc 0 (T : ℝ)))
    (hq0 : q 0=(b T : ℂ))
    (hq : ∀ t ∈ Ioc 0 (T : ℝ), HasDerivWithinAt q
      (-2/(q t-(driverValue b ((T : ℝ)-t) : ℂ))) (Ici t) t)
    (hqp : ∀ t ∈ Ioc 0 (T : ℝ), 0 < (q t).im)
    (hcone : ∀ t ∈ Icc 0 a,
      ((q t).re-driverValue b ((T : ℝ)-t))^2 ≤ t ∧ 3*t ≤ (q t).im^2) :
    q T=trace 1 b T := by
  let u (s : ℝ) := driverValue b ((T : ℝ)-s)
  have hreflect (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      (T : ℝ)-s ∈ Icc 0 (T : ℝ) :=
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  have hu (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt u
      (-b' ((T : ℝ)-s)) (Icc 0 (T : ℝ)) s := by
    have hi : HasDerivWithinAt (fun t : ℝ => (T : ℝ)-t) (-1) (Icc 0 (T : ℝ)) s := by
      simpa using ((hasDerivAt_id s).const_sub (T : ℝ)).hasDerivWithinAt
    convert! (hd _ (hreflect s hs)).comp s hi hreflect using 1
    simp only [mul_neg,mul_one]
  obtain ⟨K,_hK,hbound⟩ := exists_boundary_radial_distance_constant ha haT hL hsmall
    q u (fun t => -b' ((T : ℝ)-t)) hqc hq hqp hcone hu
    (fun t ht => by simpa only [abs_neg] using hb _ (hreflect t ht))
  have hdist (y : ℝ) (hy : 0 < y) :
      dist (q T) (inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I)) ≤ y*K := by
    let w : ℂ := (b T : ℂ)+(y : ℂ)*I
    have hw : w ∈ upperHalfPlane := by simpa [w,upperHalfPlane] using hy
    obtain ⟨r,hr0,hrp,hrd,hrT⟩ := exists_raw_reverse_trajectory b T w hw
    have he := hbound r (fun t ht => hrd t ht.1)
      (fun t ht => hy.trans_le (by simpa [w] using hrp t ht.1))
      (by simp [hr0,w,u,driverValue])
    have hzero : dist (q 0) (r 0)=y := by
      rw [hq0,hr0,dist_comm,dist_eq_norm]
      simp [w,abs_of_pos hy]
    rw [hzero,← hrT] at he
    exact he
  have hlim := tendsto_inverseFlow_smooth_trace b T b' hd hL hb
  have hdistlim : Tendsto
      (fun y : ℝ => dist (q T) (inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*I)))
      (𝓝[>] 0) (𝓝 (dist (q T) (trace 1 b T))) := tendsto_const_nhds.dist hlim
  have hzero : Tendsto (fun y : ℝ => y*K) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [id_eq,zero_mul] using
      ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const K
  apply dist_le_zero.mp
  exact le_of_tendsto_of_tendsto hdistlim hzero
    (by filter_upwards [self_mem_nhdsWithin] with y hy; exact hdist y hy)

end SLEExactGauge.Target

end

end OAI
