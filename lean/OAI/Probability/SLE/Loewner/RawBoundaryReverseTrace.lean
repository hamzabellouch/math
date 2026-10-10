import OAI.Probability.SLE.Loewner.RawBoundaryTraceIdentification
import OAI.Probability.SLE.Loewner.InitialConeFromInterval

namespace OAI

/-! Every continuous positive reverse solution issuing from the driver
ends at the prescribed raw trace. The cone estimate is derived. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem boundary_reverse_eq_trace
    (b : Driver) (T : ℝ≥0) (hT : 0 < T) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L)
    (q : ℝ → ℂ) (hqc : ContinuousOn q (Icc 0 (T : ℝ)))
    (hq0 : q 0=(b T : ℂ))
    (hq : ∀ t ∈ Ioc 0 (T : ℝ), HasDerivWithinAt q
      (-2/(q t-(driverValue b ((T : ℝ)-t) : ℂ))) (Ici t) t)
    (hqp : ∀ t ∈ Ioc 0 (T : ℝ), 0 < (q t).im) :
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
  have hzero : q 0=(u 0 : ℂ) := by simpa [u,driverValue] using hq0
  obtain ⟨c,hc,hcT,hcone⟩ := exists_initial_reverse_cone_of_interval_derivative
    (show 0 < (T : ℝ) from hT) hL q u (fun t => -b' ((T : ℝ)-t)) hqc hu hzero hq hqp
    (fun t ht => by simpa only [abs_neg] using hb _ (hreflect t ht))
  obtain ⟨a,ha,hac,hsmall⟩ := exists_smooth_window c hc L
  exact boundary_reverse_eq_trace_of_cone b T b' hd hL hb ha (hac.trans hcT) hsmall
    q hqc hq0 hq hqp (fun t ht => hcone t ⟨ht.1,ht.2.trans hac⟩)

end SLEExactGauge.Target

end

end OAI
