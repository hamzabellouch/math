import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMildStrong
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevNonlinearity

namespace OAI

/-! # Transferring the forced reduced equation to the standard Sobolev model -/

namespace DefocusingNLS

theorem hasDerivAt_expandingToSobolev_reduced (a b k L : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (w r : ℝ → FourierL2) (t : ℝ)
    (hw : HasDerivAt (fun s => lowerSobolevInclusion (w s))
      (expandingReducedField a b L w r t) t) :
    HasDerivAt (fun s => lowerSobolevInclusion (expandingToSobolev a k ha1 hk (w s)))
      (expandingReducedField a b L (fun s => expandingToSobolev a k ha1 hk (w s))
        (fun s => expandingToSobolev a k ha1 hk (r s)) t) t := by
  have h := ((expandingToSobolev a k ha1 hk).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hw
  have hreal (c : ℝ) (f : FourierL2) :
      expandingToSobolev a k ha1 hk (c • f) = c • expandingToSobolev a k ha1 hk f :=
    (expandingToSobolev a k ha1 hk).toLinearMap.map_smul_of_tower c f
  simpa only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', expandingReducedField,
    map_add, map_smul, hreal, expandingToSobolev_lowerInclusion, expandingToSobolev_lowerGenerator] using h

end DefocusingNLS

end OAI
