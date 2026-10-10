import OAI.Probability.SLE.Stochastic.DrivingLeftCluster

namespace OAI

/-! Full continuity of the actual slit driving value before the final
parameter, derived from the inverse energy and boundary noncollapse. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

theorem initialDriving_tendsto_from_left (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {s : unitInterval} (hs0 : s≠0) (hs : s<1)
    {t : ℕ → unitInterval} (hts : ∀ n, t n<s) (ht : Tendsto t atTop (𝓝 s)) :
    Tendsto (fun n => initialDriving p hi h0 hH (t n)) atTop
      (𝓝 (initialDriving p hi h0 hH s)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let M := (512*Real.pi+9)*R
  have hbound (n : ℕ) : initialDriving p hi h0 hH (t (ns n))∈Icc (-M) M := by
    rw [initialDriving_of_lt p hi h0 hH ((hts (ns n)).trans hs)]
    exact abs_le.mp (initialDrivingValue_bound p hi h0 hH hR hp _ _)
  obtain ⟨a,_,φ,hφ,hlim⟩ := isCompact_Icc.tendsto_subseq hbound
  have he := initialDriving_left_cluster p hi h0 hH hR hp hs0 hs
    (fun n => hts (ns (φ n))) ((ht.comp hns).comp hφ.tendsto_atTop) hlim
  exact ⟨φ,by simpa only [Function.comp_def,he] using hlim⟩

theorem initialDriving_continuousWithinAt_left (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s : unitInterval} (hs : s<1) :
    ContinuousWithinAt (initialDriving p hi h0 hH) (Iio s) s := by
  by_cases hs0 : s=0
  · subst s
    have hem : Iio (0:unitInterval)=∅ := by
      ext x
      simp only [mem_Iio,mem_empty_iff_false,iff_false]
      exact not_lt_of_ge (show (0:unitInterval)≤x from x.property.1)
    rw [hem]
    exact continuousWithinAt_of_notMem_closure (by simp)
  obtain ⟨R0,hRp⟩ := (isCompact_range p.continuous).isBounded.exists_norm_le
  let R := max R0 0+1
  have hR : 0<R := by dsimp [R]; positivity
  have hpR (u : unitInterval) : ‖p u‖<R :=
    (hRp _ (mem_range_self u)).trans_lt (by dsimp [R]; linarith [le_max_left R0 0])
  apply tendsto_of_seq_tendsto
  intro t ht
  have hts : ∀ᶠ n in atTop, t n<s := (tendsto_nhdsWithin_iff.mp ht).2
  obtain ⟨N,hN⟩ := eventually_atTop.mp hts
  have ht' : Tendsto (fun n => t (n+N)) atTop (𝓝 s) :=
    (ht.mono_right nhdsWithin_le_nhds).comp (tendsto_add_atTop_nat N)
  have hres := initialDriving_tendsto_from_left p hi h0 hH hR
    hpR hs0 hs
    (fun n => hN (n+N) (by omega)) ht'
  exact (tendsto_add_atTop_iff_nat N).mp hres

theorem initialDriving_continuousAt (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s : unitInterval} (hs : s<1) :
    ContinuousAt (initialDriving p hi h0 hH) s := by
  exact continuousAt_iff_continuous_left'_right'.mpr
    ⟨initialDriving_continuousWithinAt_left p hi h0 hH hs,
      initialDriving_continuousWithinAt_right p hi h0 hH hs⟩

end SLEExactGauge

end

end OAI
