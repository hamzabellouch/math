import OAI.Probability.SLE.Geometry.CenteredFutureSlit
import OAI.Probability.SLE.Loewner.CapacityRadiusBound

namespace OAI

/-! The complete mapped future slit shrinks to the driving value as its
terminal time decreases to the current time. -/
noncomputable section
open Set Filter Function Metric Complex
open scoped Topology

namespace SLEExactGauge

theorem centeredFutureArc_small (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) (hs : s<1) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (t : unitInterval) (hst : s<t) (ht : t<1),
      (t:ℝ)-(s:ℝ)<δ → ∀ u : unitInterval,
        ‖centeredFutureArc p hi h0 hH hst ht u‖<ε := by
  have hn := Metric.tendsto_nhds.mp (initialDrivingValue_spec p hi h0 hH s hs) ε hε
  obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhdsWithin_iff.mp hn
  refine ⟨δ,hδ,fun t hst ht htd u => ?_⟩
  by_cases hu : u=0
  · subst u
    simpa only [centeredFutureArc_zero,norm_zero] using hε
  have hp : 0<(u:ℝ) := unitInterval.pos_iff_ne_zero.mpr hu
  have hd : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hrpos : 0<((t:ℝ)-(s:ℝ))*(u:ℝ) := mul_pos hd hp
  have hrlt : ((t:ℝ)-(s:ℝ))*(u:ℝ)<δ := by
    have hm := mul_le_mul_of_nonneg_left u.property.2 hd.le
    linarith
  have he := hnear (show ((t:ℝ)-(s:ℝ))*(u:ℝ)∈ball (0:ℝ) δ ∩ Ioi 0 from
    ⟨by simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos hrpos] using hrlt,hrpos⟩)
  change ‖mappedFutureArc p hi h0 hH hst ht u-(_ : ℂ)‖<ε
  rw [mappedFutureArc_of_ne_zero p hi h0 hH hst ht hu]
  change dist (initialForwardChart p hi h0 hH s
    (p (slitFutureParameter s (((t:ℝ)-(s:ℝ))*(u:ℝ)))))
      (initialDrivingValue p hi h0 hH s hs:ℂ)<ε at he
  simpa only [mappedFutureRaw,dist_eq_norm] using he

theorem futureSlitChart_capacity_small (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) (hs : s<1) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (t : unitInterval) (hst : s<t) (ht : t<1),
      (t:ℝ)-(s:ℝ)<δ → (futureSlitChart p hi h0 hH hst ht).capacity≤ε^2 := by
  obtain ⟨δ,hδ,hm⟩ := centeredFutureArc_small p hi h0 hH s hs hε
  exact ⟨δ,hδ,fun t hst ht htd =>
    (futureSlitChart p hi h0 hH hst ht).capacity_le_radius_sq hε
      (fun u => (hm t hst ht htd u).le)⟩

end SLEExactGauge

end

end OAI
