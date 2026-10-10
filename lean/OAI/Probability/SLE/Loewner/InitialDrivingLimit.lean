import OAI.Probability.SLE.Loewner.InitialSlitFuture
import OAI.Probability.SLE.Loewner.SlitForwardEndpoint

namespace OAI

/-! The mapped future of a simple slit approaches a real boundary point.
This supplies the driving value directly from the prescribed arc. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem exists_initial_driving_limit (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) (hs : s<1) :
    ∃ a : ℝ, Tendsto
      (fun r : ℝ => initialForwardChart p hi h0 hH s (p (slitFutureParameter s r)))
      (𝓝[>] (0:ℝ)) (𝓝 (a:ℂ)) := by
  have hD : 0<1-(s:ℝ) := sub_pos.mpr (show (s:ℝ)<1 from hs)
  have hC : Continuous (fun r : ℝ => p (slitFutureParameter s r)) :=
    p.continuous.comp (slitFutureParameter_continuous s)
  have hz : Tendsto (fun r : ℝ => p (slitFutureParameter s r))
      (𝓝[>] (0:ℝ)) (𝓝 (p s)) := by
    have hc : Tendsto (fun r : ℝ => p (slitFutureParameter s r))
        (𝓝 (0:ℝ)) (𝓝 (p s)) := by
      simpa only [slitFutureParameter_zero] using hC.tendsto 0
    exact hc.mono_left nhdsWithin_le_nhds
  by_cases hs0 : s=0
  · refine ⟨0,?_⟩
    simpa only [hs0,initialForwardChart_zero,id_eq,h0,ofReal_zero] using hz
  · simpa only [initialForwardChart,dite_eq_right hs0] using
      (initialSlitChart p hi h0 hH s hs0).exists_forward_endpoint_limit hD hC.continuousOn
      hz (fun _ hr => slitFuturePoint_mem_domain p hi hH s hr) (slit_tip_not_mem_domain p s)

noncomputable def initialDrivingValue (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) (hs : s<1) : ℝ :=
  Classical.choose (exists_initial_driving_limit p hi h0 hH s hs)

theorem initialDrivingValue_spec (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) (hs : s<1) :
    Tendsto (fun r : ℝ => initialForwardChart p hi h0 hH s (p (slitFutureParameter s r)))
      (𝓝[>] (0:ℝ)) (𝓝 ((initialDrivingValue p hi h0 hH s hs):ℂ)) :=
  Classical.choose_spec (exists_initial_driving_limit p hi h0 hH s hs)

@[simp] theorem initialDrivingValue_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane) :
    initialDrivingValue p hi h0 hH 0 zero_lt_one=0 := by
  have hz := initialDrivingValue_spec p hi h0 hH 0 zero_lt_one
  have hC := (p.continuous.comp (slitFutureParameter_continuous 0)).tendsto 0
    |>.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 (0:ℝ) from inf_le_left)
  simp only [initialForwardChart_zero,id_eq] at hz
  change Tendsto (fun r => p (slitFutureParameter 0 r)) (𝓝[>] (0:ℝ))
    (𝓝 (p (slitFutureParameter 0 0))) at hC
  have he := tendsto_nhds_unique hz hC
  simpa only [slitFutureParameter_zero,h0,ofReal_zero,initialForwardChart_zero,id_eq,
    ofReal_eq_zero] using he

end SLEExactGauge

end

end OAI
