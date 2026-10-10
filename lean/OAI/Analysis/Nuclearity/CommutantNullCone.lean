import OAI.Analysis.PureInfiniteness.ConjugateCoefficientTest
import OAI.Analysis.Nuclearity.CommutantTensorWitness
import OAI.Analysis.PureInfiniteness.SelfAdjointCoefficientCone

namespace OAI

/-! The finite GNS common-null cone and the Hahn--Banach conclusion of
KR02 Lemma 7.18. Its elementary-span input is the application-specific
consequence of Blackadar 3.3 / Tomiyama 5; it remains explicit here. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace
open Complex selfAdjoint

namespace WeakPureInfiniteness

variable {A B I : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] [Fintype I]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

open FunctionalTensorRepresentation

variable {l : I → selfAdjoint (NormUltra.QuotientAlgebra (fun _ : ℕ => A) U) →L[ℝ] ℝ} (R : FunctionalTensorRepresentation l)

local instance nullConeOrder : PartialOrder R.C := CStarAlgebra.spectralOrder _
local instance nullConeOrdered : StarOrderedRing R.C := CStarAlgebra.spectralOrderedRing _
local instance nullConeTensorOrder : PartialOrder (MinimalTensor B R.C) := CStarAlgebra.spectralOrder _
local instance nullConeTensorOrdered : StarOrderedRing (MinimalTensor B R.C) := CStarAlgebra.spectralOrderedRing _

def FunctionalTensorRepresentation.nullCone (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N) :
    ConvexCone ℝ (WeakDual ℝ (selfAdjoint (MinimalTensor B R.C))) :=
  abelianTensorCone U hB β R.original R.η R.original_commute R.ξ

def FunctionalTensorRepresentation.inclusionFunctional (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N) :
    WeakDual ℝ (selfAdjoint (MinimalTensor B R.C)) :=
  positiveFunctionalReal (inclusionTensorFunctional hB β R.original R.η R.original_commute R.ξ)

def FunctionalTensorRepresentation.elementarySpan (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N) : Prop :=
  ∀ z : MinimalTensor B R.C,
    (∀ ψ ∈ R.nullCone U hB β, ψ ⟨star z * z, IsSelfAdjoint.star_mul_self z⟩ = 0) →
    z ∈ closure (Submodule.span ℂ {w : MinimalTensor B R.C |
      ∃ b : B, ∃ c : R.C, w = minimalElementary b c ∧
        ∀ ψ ∈ R.nullCone U hB β, ψ ⟨star w * w, IsSelfAdjoint.star_mul_self w⟩ = 0} :
      Set (MinimalTensor B R.C))

omit [Fintype I] in
theorem FunctionalTensorRepresentation.inclusionFunctional_mem_of_elementary_span (hP : MainGap.PropertyP A)
    (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N) (hspan : R.elementarySpan U hB β) :
    R.inclusionFunctional U hB β ∈ R.nullCone U hB β :=
  inclusionTensorFunctional_mem_cone_of_elementary_span U hP hB β
    R.original R.η R.original_commute R.ξ hspan

theorem FunctionalTensorRepresentation.separating_sum_nonneg_of_elementary_span (hP : MainGap.PropertyP A)
    (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N) (x : I → selfAdjoint B)
    (hspan : R.elementarySpan U hB β)
    (htest : ∀ T : B →L[ℂ] N, CompletelyPositive T →
      (T : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β →
        0 ≤ ∑ i, l i (realPart (T (x i)))) :
    0 ≤ ∑ i, l i (realPart (β (x i))) := by
  let z : selfAdjoint (MinimalTensor B R.C) := ⟨R.tensorElement x, R.tensorElement_selfAdjoint x⟩
  have hw (w : N)
      (hmem : (innerHomCompression β w : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β) :
      0 ≤ (compressedTensorFunctional hB β R.original R.η R.original_commute R.ξ w z).re := by
    have h := htest (innerHomCompression β w) (innerHomCompression_cp β w) hmem
    rw [← R.tensorFunctional_element hB (innerHomCompression β w) (innerHomCompression_cp β w) x] at h
    change 0 ≤ (representedTensorFunctional hB R.original (innerHomCompression β w)
      (innerHomCompression_cp β w) R.η R.original_commute R.ξ (R.tensorElement x)).re at h
    rw [representedTensorFunctional_inner] at h
    exact h
  have hK := abelianTensorCone_nonneg_of_coefficient_test U hB β R.π R.η R.commute
    R.ξ R.cyclic z hw
  have h := hK (R.inclusionFunctional U hB β)
    (R.inclusionFunctional_mem_of_elementary_span U hP hB β hspan)
  have he := R.tensorFunctional_element hB (starHomContinuousLinear β)
    (starHomContinuous_completelyPositive β) x
  rw [tensorFunctional, representedTensorFunctional_hom] at he
  exact he ▸ h


theorem finite_coefficient_approximation_of_commutant_span (hP : MainGap.PropertyP A)
    (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N) (x : I → selfAdjoint B)
    (hspan : ∀ (l : I → selfAdjoint N →L[ℝ] ℝ) (R : FunctionalTensorRepresentation l),
      R.elementarySpan U hB β) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : B →L[ℂ] N, CompletelyPositive T ∧
      (T : B → N) ∈ finiteUnitizedAbelianCoefficientCone U β ∧
      ‖(fun i => β (x i)) - (fun i => T (x i))‖ < ε := by
  apply finite_coefficient_approximation_of_functionals U hP β x ?_ hε
  intro l hl
  obtain ⟨R⟩ := functionalTensorRepresentation_nonempty l
  exact R.separating_sum_nonneg_of_elementary_span U hP hB β x (hspan l R) hl

end WeakPureInfiniteness

end

end OAI
