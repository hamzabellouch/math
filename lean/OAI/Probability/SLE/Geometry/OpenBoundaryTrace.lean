import OAI.Probability.SLE.Loewner.RawBoundaryReverseTrace

namespace OAI

/-! The terminal value of a reverse path does not require a derivative
beyond its interval of definition. A linear continuation supplies the
unused terminal right derivative without changing the path. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

theorem boundary_reverse_eq_trace_of_open_derivative
    (b : Driver) (T : ℝ≥0) (hT : 0 < T) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L)
    (q : ℝ → ℂ) (hqc : ContinuousOn q (Icc 0 (T : ℝ)))
    (hq0 : q 0=(b T : ℂ))
    (hq : ∀ t ∈ Ioo 0 (T : ℝ), HasDerivWithinAt q
      (-2/(q t-(driverValue b ((T : ℝ)-t) : ℂ))) (Ici t) t)
    (hqp : ∀ t ∈ Ioc 0 (T : ℝ), 0 < (q t).im) :
    q T=trace 1 b T := by
  let v : ℂ := -2/(q T-(driverValue b 0 : ℂ))
  let r (t : ℝ) : ℂ := if t ≤ T then q t else q T+(t-T) • v
  have he (t : ℝ) (ht : t ≤ T) : r t=q t := ite_eq_left ht
  have hr (t : ℝ) (ht : t ∈ Ioc 0 (T : ℝ)) : HasDerivWithinAt r
      (-2/(r t-(driverValue b ((T : ℝ)-t) : ℂ))) (Ici t) t := by
    by_cases htT : t < T
    · have hevent : r =ᶠ[𝓝[Ici t] t] q := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs
        exact he s hs.le
      rw [he t ht.2]
      exact (hq t ⟨ht.1,htT⟩).congr_of_eventuallyEq hevent (he t ht.2)
    · have htEq : t=(T : ℝ) := le_antisymm ht.2 (le_of_not_gt htT)
      subst t
      have hevent : r =ᶠ[𝓝[Ici (T : ℝ)] (T : ℝ)]
          (fun s : ℝ => q T+(s-T) • v) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        by_cases hsT : s ≤ T
        · have heq : s=(T : ℝ) := le_antisymm hsT hs
          subst s
          simp [r]
        · exact ite_eq_right hsT
      have hh : HasDerivWithinAt (fun s : ℝ => q T+(s-T) • v) v (Ici (T : ℝ)) T := by
        convert! ((((hasDerivAt_id (T : ℝ)).sub_const (T : ℝ)).smul_const v).const_add
          (q T)).hasDerivWithinAt using 1
        simp only [one_smul]
      have hh' := hh.congr_of_eventuallyEq hevent (by simp [r])
      simpa only [he (T : ℝ) le_rfl,sub_self,v] using hh'
  have hrc : ContinuousOn r (Icc 0 (T : ℝ)) := by
    apply hqc.congr
    intro t ht
    exact he t ht.2
  have hz : r 0=(b T : ℂ) := (he 0 T.coe_nonneg).trans hq0
  have hh := boundary_reverse_eq_trace b T hT b' hd hL hb r hrc hz hr
    (fun t ht => by rw [he t ht.2]; exact hqp t ht)
  simpa only [he (T : ℝ) le_rfl] using hh

end SLEExactGauge.Target

end

end OAI
