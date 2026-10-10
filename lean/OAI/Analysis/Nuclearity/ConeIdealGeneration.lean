import OAI.Analysis.Nuclearity.PositiveConeNullIdeal
import OAI.Analysis.Nuclearity.ElementaryGeneratedIdeal
import OAI.Analysis.Nuclearity.CommutantNullCone

namespace OAI

/-! The precise common-null ideal in KR02 Lemma 7.18 inherits elementary
span from closed tensor-ideal generation. This is a structural bridge,
not an assumption that nuclearity has already supplied ideal generation. -/

noncomputable section
open scoped Topology ComplexOrder

namespace WeakPureInfiniteness

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder (MinimalTensor B C)] [StarOrderedRing (MinimalTensor B C)]

theorem common_null_elementary_span_of_generation
    (hgen : ∀ J : NonunitalClosedIdeal.Ideal (MinimalTensor B C),
      (elementaryGeneratedIdeal J).module = J.module)
    (K : Set (WeakDual ℝ (selfAdjoint (MinimalTensor B C))))
    (hpos : ∀ φ ∈ K, ∀ a : selfAdjoint (MinimalTensor B C),
      0 ≤ (a : MinimalTensor B C) → 0 ≤ φ a)
    (hconj : ∀ φ ∈ K, ∀ d : MinimalTensor B C, conjugateRealFunctional φ d ∈ K)
    (z : MinimalTensor B C)
    (hz : ∀ φ ∈ K, φ ⟨star z * z, IsSelfAdjoint.star_mul_self z⟩ = 0) :
    z ∈ closure (Submodule.span ℂ {w : MinimalTensor B C |
      ∃ b c, w = minimalElementary b c ∧
        ∀ φ ∈ K, φ ⟨star w * w, IsSelfAdjoint.star_mul_self w⟩ = 0} : Set (MinimalTensor B C)) := by
  let J := realPositiveConeNullIdeal K hpos hconj
  have hzJ : z ∈ J.module := (mem_realPositiveConeNullIdeal_iff K hpos hconj z).mpr hz
  have hg : z ∈ (elementaryGeneratedIdeal J).module := by rwa [hgen J]
  change z ∈ closure (Submodule.span ℂ {w : MinimalTensor B C |
    ∃ b c, w = minimalElementary b c ∧ w ∈ J.module} : Set (MinimalTensor B C)) at hg
  simpa only [J, mem_realPositiveConeNullIdeal_iff] using hg

section Application

variable {A D I : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D] [TopologicalSpace.SeparableSpace D] [Fintype I]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]
  {l : I → selfAdjoint (NormUltra.QuotientAlgebra (fun _ : ℕ => A) U) →L[ℝ] ℝ}
  (R : FunctionalTensorRepresentation l)

local instance coneGenerationOrder : PartialOrder (MinimalTensor D R.C) := CStarAlgebra.spectralOrder _
local instance coneGenerationOrdered : StarOrderedRing (MinimalTensor D R.C) := CStarAlgebra.spectralOrderedRing _

omit [TopologicalSpace.SeparableSpace D] [Fintype I] [Fact ((U : Filter ℕ) ≤ Filter.atTop)] in
theorem FunctionalTensorRepresentation.elementarySpan_of_ideal_generation
    (hD : Nuclear D) (β : D →⋆ₙₐ[ℂ] NormUltra.QuotientAlgebra (fun _ : ℕ => A) U)
    (hgen : ∀ J : NonunitalClosedIdeal.Ideal (MinimalTensor D R.C),
      (elementaryGeneratedIdeal J).module = J.module) : R.elementarySpan U hD β := by
  intro z hz
  apply common_null_elementary_span_of_generation hgen (R.nullCone U hD β) ?_ ?_ z hz
  · exact fun φ hφ => conjugateGeneratedCone_nonneg _ hφ
  · exact fun φ hφ d => conjugateGeneratedCone_conjugate _ d φ hφ

end Application
end WeakPureInfiniteness

end

end OAI
