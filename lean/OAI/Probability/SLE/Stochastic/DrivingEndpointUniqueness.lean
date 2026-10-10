import OAI.Probability.SLE.Geometry.ShrinkingPhysicalSegments
import OAI.Probability.SLE.Loewner.SlitBoundaryFiber

namespace OAI

/-! The two ends of a shrinking mapped future cannot have different
real limits: a separating real interval would collapse in the inverse. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology

namespace SLEExactGauge

theorem initialDriving_shrinking_endpoint_unique (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {s : unitInterval} (hs : s≠0) {t r : ℕ → unitInterval}
    (ht : Tendsto t atTop (𝓝 s)) (hr : Tendsto r atTop (𝓝 s))
    (htr : ∀ n, t n<r n) (hr1 : ∀ n, r n<1) {a b : ℝ}
    (ha : Tendsto (fun n => initialDrivingValue p hi h0 hH (t n) ((htr n).trans (hr1 n)))
      atTop (𝓝 a))
    (hb : Tendsto (fun n => initialForwardChart p hi h0 hH (t n) (p (r n)))
      atTop (𝓝 (b:ℂ))) : a=b := by
  by_contra hab
  have hb' := Complex.continuous_re.continuousAt.tendsto.comp hb
  simp only [ofReal_re] at hb'
  have hex : ∃ A B : ℝ, A<B ∧ ∀ᶠ n in atTop, ∀ x∈Ioo A B,
      x∈Ioo (initialDrivingValue p hi h0 hH (t n) ((htr n).trans (hr1 n)))
        (initialForwardChart p hi h0 hH (t n) (p (r n))).re ∨
      x∈Ioo (initialForwardChart p hi h0 hH (t n) (p (r n))).re
        (initialDrivingValue p hi h0 hH (t n) ((htr n).trans (hr1 n))) := by
    rcases lt_or_gt_of_ne hab with hab | hba
    · refine ⟨(2*a+b)/3,(a+2*b)/3,by linarith,?_⟩
      filter_upwards [ha.eventually (gt_mem_nhds (show a<(2*a+b)/3 by linarith)),
        hb'.eventually (lt_mem_nhds (show (a+2*b)/3<b by linarith))] with n hn hm
      intro x hx
      exact Or.inl ⟨hn.trans hx.1,hx.2.trans hm⟩
    · refine ⟨(2*b+a)/3,(b+2*a)/3,by linarith,?_⟩
      filter_upwards [hb'.eventually (gt_mem_nhds (show b<(2*b+a)/3 by linarith)),
        ha.eventually (lt_mem_nhds (show (b+2*a)/3<a by linarith))] with n hn hm
      intro x hx
      exact Or.inr ⟨hn.trans hx.1,hx.2.trans hm⟩
  obtain ⟨A,B,hAB,hcross⟩ := hex
  obtain ⟨ε,hε,hbound⟩ := shrinking_physical_segment_bound p ht hr (fun n => (htr n).le)
  let η := fun n => Real.sqrt (2*(initialCapacity p hi h0 hH (r n)-
    initialCapacity p hi h0 hH (t n)))
  have hη : Tendsto η atTop (𝓝 0) := by
    have hcap := ((initialCapacity_continuous p hi h0 hH).tendsto s).comp hr
    have hcap' := ((initialCapacity_continuous p hi h0 hH).tendsto s).comp ht
    simpa only [sub_self,mul_zero,Real.sqrt_zero,Function.comp_def,η] using
      (hcap.sub hcap').const_mul 2 |>.sqrt
  obtain ⟨Fbar,hFbar,hFe⟩ := (initialSlitChart p hi h0 hH s hs).exists_boundary_extension
  have hFi : ∀ z∈upperHalfPlane, Fbar z=initialInverseChart p hi h0 hH s z := by
    intro z hz
    simpa only [initialInverseChart,dite_eq_right hs] using hFe z hz
  have hlow : ∀ᶠ n in atTop, ∀ x∈Ioo A B, ∃ y∈Ioc 0 (η n),
      ‖initialInverseChart p hi h0 hH (t n) ((x:ℂ)+(y:ℂ)*I)-p s‖≤ε n := by
    filter_upwards [hcross] with n hn
    intro x hx
    exact mappedFutureArc_thin_crossing p hi h0 hH (htr n) (hr1 n) (p s) (hn x hx)
      (fun v hv => hbound n v ⟨hv.1.le,hv.2⟩)
  have hconst := initialInverse_thin_crossing_collapse p hi h0 hH hR hp ht hFbar hFi hε hη hlow
  apply (initialSlitChart p hi h0 hH s hs).boundary_not_constant_on_interval
    hFbar hFe ((A+B)/2) (show 0<(B-A)/2 by linarith) (p s)
  intro x hx
  exact hconst x ⟨by linarith [hx.1],by linarith [hx.2]⟩

end SLEExactGauge

end

end OAI
