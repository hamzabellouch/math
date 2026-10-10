import OAI.Analysis.KadisonSimilarity.FreeProduct.DyadicHaarUnitary
import OAI.Analysis.KadisonSimilarity.FreeProduct.SmallFreeCornerData

namespace OAI

/-! The precise diffuse-corner Haar input used by the free-corner argument
is supplied by the constructed dyadic unitary. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra K}

local instance concreteHaar_closed : IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K)) :=
  Generator.Tracial.base_norm_closed N

theorem thielDiffuseCornerHaarInput (τ : TracialRepresentation N)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q) : ThielDiffuseCornerHaarInput τ := by
  intro q hq _
  exact exists_dyadicCornerHaar τ hdiff ⟨q, hq⟩

/-- A diffuse concrete source supplies the small corner, containing half
projection and Haar unitary with no independent Haar existence premise. -/
theorem exists_concreteSmallFreeCornerData_of_diffuse
    (τ : TracialRepresentation N)
    (hdiff : ∀ p : N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧
        p * q = q ∧ q * p = q)
    {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Nonempty (I j)]
    (V : N.toStarSubalgebra →ₗ[ℂ] H)
    (M : NestedTracialMatrices (A := I) (concreteTraceLinear τ) V)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ))
      Filter.atTop Filter.atTop)
    {s : ℝ} (hs : 0 < s) : Nonempty (SmallFreeCornerData (concreteTraceLinear τ) s) :=
  exists_concreteSmallFreeCornerData τ hdiff (thielDiffuseCornerHaarInput τ hdiff)
    V M hsize hs

end KadisonSimilarity

end

end OAI
