import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem IsFaithfulTracialVector.isNormalFaithfulTracialState
    {M : VonNeumannAlgebra E} {ξ : E} (hξ : IsFaithfulTracialVector M ξ) :
    IsNormalFaithfulTracialState M hξ.toTracialState := by
  constructor
  · intro a ha hzero
    apply Subtype.ext
    exact hξ.2.2 (a : E →L[ℂ] E) a.property ha hzero
  · intro ι L _hL a b _hbound hstrong
    change Tendsto (fun i => inner ℂ ξ ((a i : E →L[ℂ] E) ξ)) L
      (𝓝 (inner ℂ ξ ((b : E →L[ℂ] E) ξ)))
    exact tendsto_const_nhds.inner (hstrong ξ)

end Invariant233

end

end OAI
