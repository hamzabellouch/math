import OAI.Algebra.DepthFive.Basic

namespace OAI

namespace Problem335

/-- The numerical size estimate used after instantiating the block circuit. -/
theorem circuitSize_le_block_bound {K : Type*} [CommSemiring K] {n r t : ℕ}
    (c : Depth5Circuit K n)
    (hleaf : c.leafCount ≤ n ^ 3)
    (hbottom : c.bottomCount ≤ n ^ 3)
    (hlower : c.lowerCount ≤ r * n ^ (t + 1))
    (hmiddle : c.middleCount ≤ r * n ^ 2)
    (hupper : c.upperCount ≤ n ^ (r - 1)) :
    circuitSize c ≤ 2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) +
      n ^ (r - 1) + 1 := by
  unfold circuitSize
  omega

/-- Specialization of the block count to the precise upper gate bound. -/
theorem circuitSize_le_upperGateBound {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n)
    (hleaf : c.leafCount ≤ n ^ 3)
    (hbottom : c.bottomCount ≤ n ^ 3)
    (hlower : c.lowerCount ≤ ceilDiv n (ceilSqrt n) * n ^ (ceilSqrt n + 1))
    (hmiddle : c.middleCount ≤ ceilDiv n (ceilSqrt n) * n ^ 2)
    (hupper : c.upperCount ≤ n ^ (ceilDiv n (ceilSqrt n) - 1)) :
    circuitSize c ≤ upperGateBound n := by
  exact circuitSize_le_block_bound c hleaf hbottom hlower hmiddle hupper

end Problem335

end OAI
