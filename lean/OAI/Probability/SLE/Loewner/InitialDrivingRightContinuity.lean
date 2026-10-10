import OAI.Probability.SLE.Loewner.InitialDrivingIncrement
import OAI.Probability.SLE.Loewner.FutureSlitRadius

namespace OAI

/-! Right continuity of the actual driving value follows from shrinking
mapped future slits and the uniform boundary-coordinate estimate. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

noncomputable def initialDriving (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) : ℝ :=
  if hs : s<1 then initialDrivingValue p hi h0 hH s hs else 0

lemma initialDriving_of_lt (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s : unitInterval} (hs : s<1) :
    initialDriving p hi h0 hH s=initialDrivingValue p hi h0 hH s hs := dite_eq_left hs

theorem initialDriving_continuousWithinAt_right (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s : unitInterval} (hs : s<1) :
    ContinuousWithinAt (initialDriving p hi h0 hH) (Ioi s) s := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := 512*Real.pi+9
  have hC : 0<C := by dsimp only [C]; positivity
  let R : ℝ := ε/(2*C)
  have hR : 0<R := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨δ,hδ,hsmall⟩ := centeredFutureArc_small p hi h0 hH s hs hR
  have htime : Tendsto (fun t : unitInterval => (t:ℝ)-(s:ℝ)) (𝓝[>] s) (𝓝 0) := by
    have hc : Continuous (fun t : unitInterval => (t:ℝ)-(s:ℝ)) :=
      continuous_subtype_val.sub continuous_const
    have hh := (hc.tendsto s).mono_left (show 𝓝[>] s≤𝓝 s from inf_le_left)
    simpa only [sub_self] using hh
  filter_upwards [self_mem_nhdsWithin,htime.eventually (gt_mem_nhds hδ),
    Filter.Eventually.filter_mono inf_le_left (gt_mem_nhds hs)] with t hst htd ht
  rw [Real.dist_eq,initialDriving_of_lt p hi h0 hH ht,initialDriving_of_lt p hi h0 hH hs]
  have hb := initialDriving_increment_bound p hi h0 hH hst ht hR (hsmall t hst ht htd)
  apply hb.trans_lt
  change C*R<ε
  dsimp only [R]
  have he : C*(ε/(2*C))=ε/2 := by field_simp
  rw [he]
  linarith

end SLEExactGauge

end

end OAI
