import OAI.Geometry.RCD.Transport.ContinuousLengthDistortion
import OAI.Geometry.RCD.Sobolev.WeakEndpointWeights

namespace OAI

/-! # Reduced distortion as a bounded continuous path test -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

def pathDistortion (K N t : ℝ) (hK : K≤0) (hN : 1<N) (ht : 0≤t) (ht1 : t≤1) :
    C(Time,X) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun γ => (sigma K N t (dist (γ 0) (γ 1))).toReal,by
      have hh : Continuous (fun γ : C(Time,X) => sigma K N t (dist (γ 0) (γ 1))) :=
        (continuous_sigma_nonpos_length hK hN ht ht1).comp
          ((continuous_eval_const 0).nndist (continuous_eval_const 1))
      exact continuous_iff_continuousAt.mpr (fun γ =>
        (ENNReal.continuousAt_toReal (sigma_nonpos_ne_top (t:=t)
          (d:=dist (γ 0) (γ 1)) hK hN dist_nonneg)).comp
            (f:=fun η : C(Time,X) => sigma K N t (dist (η 0) (η 1))) hh.continuousAt)⟩
    1 (by
      intro γ η
      have hb (ζ : C(Time,X)) : 0≤(sigma K N t (dist (ζ 0) (ζ 1))).toReal ∧
          (sigma K N t (dist (ζ 0) (ζ 1))).toReal≤1 := by
        refine ⟨ENNReal.toReal_nonneg,?_⟩
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (sigma_nonpos_le_time hK hN ht ht1 dist_nonneg)).trans
          (by simpa only [ENNReal.toReal_ofReal ht] using ht1)
      change |(sigma K N t (dist (γ 0) (γ 1))).toReal-
        (sigma K N t (dist (η 0) (η 1))).toReal|≤1
      exact abs_le.mpr ⟨by linarith [(hb γ).1,(hb η).2],by linarith [(hb γ).2,(hb η).1]⟩)

end RegularPointCoordinates

end

end OAI
