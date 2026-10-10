import OAI.Analysis.PureInfiniteness.ConjugateGeneratedCone
import OAI.Analysis.Nuclearity.TensorFixedElement
import OAI.Analysis.Nuclearity.PositiveSquareNullSpace

namespace OAI

/-! The tensor-functional cone in KR02 Lemma 7.18. The nullspace argument
uses the elementary-span property of its closed tensor ideal
(Blackadar 3.3 / Tomiyama 5). -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

variable {A B C H : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [CStarAlgebra C] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local instance coneTensorOrder : PartialOrder (MinimalTensor B C) := CStarAlgebra.spectralOrder _
local instance coneTensorOrdered : StarOrderedRing (MinimalTensor B C) := CStarAlgebra.spectralOrderedRing _

def abelianCompressionIndex (β : B →⋆ₙₐ[ℂ] N) :=
  {v : N // ∀ b c, Commute (innerHomCompression β v b) (innerHomCompression β v c)}

def abelianTensorCone (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N)
    (π : N →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) :
    ConvexCone ℝ (WeakDual ℝ (selfAdjoint (MinimalTensor B C))) :=
  conjugateGeneratedCone (fun v : abelianCompressionIndex U β =>
    compressedTensorFunctional hB β π η hc ξ v.val)

theorem inclusionTensorFunctional_mem_cone_of_elementary_span
    (hP : MainGap.PropertyP A) (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N)
    (π : N →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H)
    (hspan : ∀ z : MinimalTensor B C,
      (∀ ψ ∈ abelianTensorCone U hB β π η hc ξ,
        ψ ⟨star z * z, IsSelfAdjoint.star_mul_self z⟩ = 0) →
      z ∈ closure (Submodule.span ℂ {w : MinimalTensor B C |
        ∃ b : B, ∃ c : C, w = minimalElementary b c ∧
          ∀ ψ ∈ abelianTensorCone U hB β π η hc ξ,
            ψ ⟨star w * w, IsSelfAdjoint.star_mul_self w⟩ = 0} : Set (MinimalTensor B C))) :
    positiveFunctionalReal (inclusionTensorFunctional hB β π η hc ξ) ∈
      abelianTensorCone U hB β π η hc ξ := by
  let K := abelianTensorCone U hB β π η hc ξ
  let Φ := inclusionTensorFunctional hB β π η hc ξ
  have hzero : (0 : WeakDual ℝ (selfAdjoint (MinimalTensor B C))) ∈ K :=
    conjugateGeneratedCone_zero _
  have hzeroSet : (0 : WeakDual ℝ (selfAdjoint (MinimalTensor B C))) ∈
      (K : Set (WeakDual ℝ (selfAdjoint (MinimalTensor B C)))) := hzero
  have hnull (z : MinimalTensor B C)
      (hz : ∀ ψ ∈ K, ψ ⟨star z * z, IsSelfAdjoint.star_mul_self z⟩ = 0) :
      Φ (star z * z) = 0 := by
    apply positiveFunctional_square_null_of_closure_span Φ _ _ (hspan z hz)
    rintro w ⟨b, c, rfl, hw⟩
    obtain ⟨v, _, hab, he⟩ := abelian_compression_tensor_square_witness U hP hB β π η hc ξ b c
    let i : abelianCompressionIndex U β := ⟨v, hab⟩
    have hmem : positiveFunctionalReal (compressedTensorFunctional hB β π η hc ξ v) ∈ K :=
      conjugateGeneratedCone_base _ i
    have hv := hw _ hmem
    change (compressedTensorFunctional hB β π η hc ξ v
      (star (minimalElementary b c) * minimalElementary b c)).re = 0 at hv
    have hre : (Φ (star (minimalElementary b c) * minimalElementary b c)).re = 0 :=
      (congrArg Complex.re he).trans hv
    apply Complex.ext hre
    exact (map_nonneg Φ (star_mul_self_nonneg _)).2.symm
  change positiveFunctionalReal Φ ∈ (K : Set _)
  refine mem_positive_cone_of_common_nullspace (K : Set _) ?_ ?_ ?_ ?_ ?_ ?_
    (positiveFunctionalReal Φ) ?_ ?_
  · exact isClosed_closure
  · exact K.convex
  · exact hzero
  · intro t ht ψ hψ
    rcases ht.eq_or_lt with rfl | ht
    · simpa only [zero_smul] using hzeroSet
    · exact K.smul_mem ht hψ
  · exact fun ψ hψ => conjugateGeneratedCone_nonneg _ hψ
  · exact fun ψ hψ d => conjugateGeneratedCone_conjugate _ d ψ hψ
  · exact positiveFunctionalReal_nonneg Φ
  · intro z hz
    change (Φ (star z * z)).re = 0
    rw [hnull z hz]
    rfl

end WeakPureInfiniteness

end

end OAI
