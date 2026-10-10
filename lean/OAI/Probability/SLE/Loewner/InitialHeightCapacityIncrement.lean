import OAI.Probability.SLE.Loewner.ForwardHeightSquareIncrement

namespace OAI

/-! Height loss on a surviving initial-slit prefix is bounded by twice
the exact capacity increment. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem initialForward_height_capacity_increment (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s r T : unitInterval} (hsr : s≤r) (hrT : r≤T) (hT : T<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p T)) :
    (initialForwardChart p hi h0 hH s z).im^2≤
      (initialForwardChart p hi h0 hH r z).im^2+
        2*(initialCapacity p hi h0 hH r-initialCapacity p hi h0 hH s) := by
  have ha := initialCapacity_nonneg p hi h0 hH s
  have hsr' := initialCapacity_monotone p hi h0 hH hsr
  have hrT' := initialCapacity_monotone p hi h0 hH hrT
  have hc : ContinuousOn (capacityForwardOnPrefix p hi h0 hH T z)
      (Icc (initialCapacity p hi h0 hH s) (initialCapacity p hi h0 hH r)) :=
    (capacityForwardOnPrefix_lipschitz p hi h0 hH hT hz).continuous.continuousOn
  have hd (c : ℝ) (hcc : c∈Ico (initialCapacity p hi h0 hH s)
      (initialCapacity p hi h0 hH r)) :
      HasDerivWithinAt (capacityForwardOnPrefix p hi h0 hH T z)
        (1/(capacityForwardOnPrefix p hi h0 hH T z c-
          (capacityDriverOnPrefix p hi h0 hH T hT c:ℂ))) (Ici c) c :=
    capacityForward_hasDerivWithinAt_Ici p hi h0 hH hT hz
      ⟨ha.trans hcc.1,hcc.2.trans_le hrT'⟩
  have hh := height_square_increment hsr' hc hd
  simpa only [capacityForwardOnPrefix_at_initialCapacity p hi h0 hH T z (hsr.trans hrT),
    capacityForwardOnPrefix_at_initialCapacity p hi h0 hH T z hrT] using hh

end SLEExactGauge

end

end OAI
