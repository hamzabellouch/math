import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalPolynomial

namespace OAI

/-! # Finite physical Fourier sums converge to the actual torus function -/

open Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_expandingPhysicalPolynomial (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (y : E) (t : Icc (0 : ℝ) T) :
    Tendsto (fun S : Finset frequencyLattice => expandingPhysicalPolynomial a k L T hT u S y t)
      atTop (𝓝 (expandingTorusFunction a k (expandingRadius L t) (u t)
        (euclideanToTorus ((expandingRadius L t)⁻¹ • y)))) := by
  have hR : 1 ≤ expandingRadius L t := hL.trans (expandingRadius_ge L t hL t.2.1)
  have h := (summable_expandingTorusTerm a k (expandingRadius L t) ha ha1 hk hR (u t)).hasSum.mapL
    (ContinuousMap.evalCLM (R := ℂ) (euclideanToTorus ((expandingRadius L t)⁻¹ • y)))
  change Tendsto _ atTop _ at h
  simpa [expandingPhysicalPolynomial, projIcc_of_mem hT t.2,
    expandingTorusTerm, ContinuousMap.smul_apply, smul_eq_mul,
    torusCharacter_euclidean, expandingTorusFunction] using h

end DefocusingNLS

end OAI
