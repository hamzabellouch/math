import OAI.Analysis.StructuralCrouzeix.GeometryBasics

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology

lemma LocalAnalyticBoundary.closedSide {U : Set ℂ} {p : ℂ}
    (h : LocalAnalyticBoundary U p) : LocalClosedAnalyticBoundary U p := by
  obtain ⟨χ,hχ0,hχa,hχd,hs,hb⟩ := h
  obtain ⟨V,hVo,h0V,hχVo,ψ,hψa,hleft,hright⟩ :=
    analytic_local_inverse_neighborhood hχa hχd
  have hVevent : ∀ᶠ z : ℂ in 𝓝 0, z ∈ V := hVo.mem_nhds h0V
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp
    (hVevent.and (hs.and hb))
  refine ⟨χ,hχ0,hχa,hχd,hs,hb,?_⟩
  apply mem_of_superset (ball_mem_nhds 0 hr)
  intro z hz
  have hzV : z ∈ V := (hrall hz).1
  have hzψ : ψ (χ z) = z := hleft z hzV
  have hzimage : χ z ∈ χ '' V := ⟨z,hzV,rfl⟩
  constructor
  · intro hcl
    by_contra hn
    have him : z.im < 0 := lt_of_not_ge hn
    have hψc : ContinuousAt ψ (χ z) := (hψa (χ z) hzimage).continuousAt
    have hnear : ∀ᶠ y in 𝓝 (χ z), ψ y ∈ ball 0 r :=
      hψc.preimage_mem_nhds (by simpa only [hzψ] using isOpen_ball.mem_nhds hz)
    have him_cont : Tendsto (fun y : ℂ => (ψ y).im) (𝓝 (χ z))
        (𝓝 ((ψ (χ z)).im)) := Complex.continuous_im.continuousAt.comp hψc
    have hnegative : ∀ᶠ y in 𝓝 (χ z), (ψ y).im < 0 :=
      him_cont.eventually (by simpa only [hzψ] using (gt_mem_nhds him))
    have hnot : ∀ᶠ y in 𝓝 (χ z), y ∉ U := by
      filter_upwards [hχVo.mem_nhds hzimage,hnear,hnegative] with y hy hry hiy
      intro hyU
      have hχU : χ (ψ y) ∈ U := by rw [hright y hy]; exact hyU
      have hi := (hrall hry).2.1.mp hχU
      exact (not_lt_of_ge hiy.le) hi
    obtain ⟨_,hyU,hyn⟩ :=
      ((mem_closure_iff_frequently.mp hcl).and_eventually hnot).exists
    exact hyn hyU
  · intro him
    rcases eq_or_lt_of_le him with heq | hpos
    · exact ((hrall hz).2.2 heq.symm).1
    · exact subset_closure ((hrall hz).2.1.mpr hpos)

lemma convex_analytic_exterior_coordinate {U : Set ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hK : IsCompact (closure U))
    {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, LocalAnalyticBoundary U p) :
    Nonempty (ExteriorCoordinate U) :=
  convex_closed_analytic_exterior_coordinate hU hcv hK ha
    (fun p hp => (hchart p hp).closedSide)

end CompleteCrouzeix
end

end OAI
