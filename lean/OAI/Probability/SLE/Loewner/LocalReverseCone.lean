import OAI.Probability.SLE.Loewner.ReverseBoundaryCone

namespace OAI

/-! A continuous positive reverse solution starting at the driver is
non-tangential on a sufficiently short initial interval. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology

namespace SLEExactGauge

theorem exists_initial_reverse_cone {T L : ℝ} (hT : 0 < T) (hL : 0 ≤ L)
    (q : ℝ → ℂ) (u u' : ℝ → ℝ)
    (hc : ContinuousOn q (Icc 0 T)) (huc : ContinuousOn u (Icc 0 T))
    (hq0 : q 0=(u 0 : ℂ))
    (hq : ∀ t ∈ Ioc 0 T, HasDerivWithinAt q
      (-2/(q t-(u t : ℂ))) (Ici t) t)
    (hu : ∀ t ∈ Ioc 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hp : ∀ t ∈ Ioc 0 T, 0 < (q t).im)
    (hb : ∀ t ∈ Ioc 0 T, |u' t| ≤ L) :
    ∃ a : ℝ, 0 < a ∧ a ≤ T ∧
      ∀ t ∈ Icc 0 a, ((q t).re-u t)^2 ≤ t ∧ 3*t ≤ (q t).im^2 := by
  let M : ℝ := 1/(2*(L+1))
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hsmall : 2*L*M ≤ 1 := by
    have hd : 0 < 2*(L+1) := by positivity
    calc
      2*L*M = (2*L)/(2*(L+1)) := by dsimp [M]; ring
      _ ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hc0 := ((hc.sub (Complex.continuous_ofReal.comp_continuousOn huc)) 0 ⟨le_rfl,hT.le⟩).norm
  have hv : ‖q 0-(u 0 : ℂ)‖ < M := by simpa only [hq0,sub_self,norm_zero] using hMpos
  have he : ∀ᶠ t in 𝓝[Icc 0 T] 0, ‖q t-(u t : ℂ)‖ < M :=
    hc0.eventually (Iio_mem_nhds hv)
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhdsWithin_iff.mp he
  let a : ℝ := min T (δ/2)
  have ha : 0 < a := lt_min hT (half_pos hδ)
  have haT : a ≤ T := min_le_left _ _
  have hsub : Icc 0 a ⊆ Icc 0 T := Icc_subset_Icc_right haT
  have hsub' : Ioc 0 a ⊆ Ioc 0 T := Ioc_subset_Ioc_right haT
  refine ⟨a,ha,haT,reverse_boundary_cone_of_small_center ha.le hL hsmall q u u'
    (hc.mono hsub) (huc.mono hsub) hq0
    (fun t ht => hq t (hsub' ht)) (fun t ht => hu t (hsub' ht))
    (fun t ht => hp t (hsub' ht)) (fun t ht => hb t (hsub' ht)) ?_⟩
  intro t ht
  apply le_of_lt
  apply hδb
  refine ⟨?_,hsub (Ioc_subset_Icc_self ht)⟩
  rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht.1]
  exact (ht.2.trans (min_le_right _ _)).trans_lt (half_lt_self hδ)

end SLEExactGauge

end

end OAI
