import OAI.Probability.SLE.Loewner.InitialDrivingContinuity

namespace OAI

/-! Continuity of the driver and Loewner kernel in the exact capacity clock. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem capacityDriverOnPrefix_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) :
    Continuous (capacityDriverOnPrefix p hi h0 hH T hT) := by
  rw [continuous_iff_continuousAt]
  intro c
  have he : capacityDriverOnPrefix p hi h0 hH T hT=
      initialDriving p hi h0 hH ∘ capacityParameterOnPrefix p hi h0 hH T := by
    funext u
    exact (initialDriving_of_lt p hi h0 hH
      ((capacityParameterOnPrefix_le p hi h0 hH T u).trans_lt hT)).symm
  rw [he]
  exact (initialDriving_continuousAt p hi h0 hH
    ((capacityParameterOnPrefix_le p hi h0 hH T c).trans_lt hT)).comp
      (capacityParameterOnPrefix_continuous p hi h0 hH T).continuousAt

theorem capacityLoewnerKernel_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {T : unitInterval} (hT : T<1) {z : ℂ}
    (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    Continuous (fun c : ℝ => 1/(capacityForwardOnPrefix p hi h0 hH T z c-
      (capacityDriverOnPrefix p hi h0 hH T hT c:ℂ))) := by
  have hf := (capacityForwardOnPrefix_lipschitz p hi h0 hH hT hz).continuous
  have hu := Complex.continuous_ofReal.comp (capacityDriverOnPrefix_continuous p hi h0 hH hT)
  refine continuous_const.div (hf.sub hu) ?_
  intro c he
  have him := congrArg Complex.im he
  have hpos : 0<(capacityForwardOnPrefix p hi h0 hH T z c).im :=
    initialForwardChart_im_pos p hi h0 hH _
      ⟨hz.1,fun he => hz.2 (initialSubarc_range_mono p
        (capacityParameterOnPrefix_le p hi h0 hH T c) he)⟩
  simp only [sub_im,ofReal_im,sub_zero,zero_im] at him
  linarith

end SLEExactGauge

end

end OAI
