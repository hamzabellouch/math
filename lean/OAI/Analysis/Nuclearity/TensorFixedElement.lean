import OAI.Analysis.Nuclearity.NuclearTensorFunctional
import OAI.Analysis.PureInfiniteness.AbelianPositiveFixer

namespace OAI

/-! The elementary-tensor nullspace test in the last paragraph of KR02
Lemma 7.18. The fixing map is an actual abelian-range inner compression. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

variable {B C D H : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C]
  [NonUnitalCStarAlgebra D] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance fixedTensorOrder : PartialOrder (MinimalTensor B C) := CStarAlgebra.spectralOrder _
local instance fixedTensorOrdered : StarOrderedRing (MinimalTensor B C) := CStarAlgebra.spectralOrderedRing _

omit [PartialOrder B] [StarOrderedRing B] in
def representedCompression (β : B →⋆ₙₐ[ℂ] D) (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (v : D) : B →L[ℂ] (H →L[ℂ] H) :=
  innerHomCompression (π.comp β) (π v)

omit [PartialOrder B] [StarOrderedRing B] in
lemma representedCompression_apply (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (v : D) (b : B) :
    representedCompression β π v b = π (star v * β b * v) := by
  simp only [representedCompression, innerHomCompression_apply,
    NonUnitalStarAlgHom.comp_apply, map_mul, map_star]

lemma representedCompression_cp (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (v : D) :
    CompletelyPositive (representedCompression β π v) :=
  innerHomCompression_cp (π.comp β) (π v)

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C] in
lemma representedCompression_commute (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (v : D) (b : B) (c : C) :
    Commute (representedCompression β π v b) (η c) := by
  rw [representedCompression_apply]
  exact hc _ _

def compressedTensorFunctional (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) (v : D) :
    MinimalTensor B C →ₚ[ℂ] ℂ :=
  nuclearTensorFunctional hB (representedCompression β π v)
    (representedCompression_cp β π v) η
    (representedCompression_commute β π η hc v) ξ

def inclusionTensorFunctional (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) :
    MinimalTensor B C →ₚ[ℂ] ℂ :=
  nuclearTensorFunctional hB (innerHomCompression (π.comp β) 1)
    (innerHomCompression_cp (π.comp β) 1) η
    (fun b c => by simpa only [innerHomCompression_apply, star_one, one_mul,
      mul_one, NonUnitalStarAlgHom.comp_apply] using hc (β b) c) ξ

lemma compressedTensorFunctional_elementary (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) (v : D) (b : B) (c : C) :
    compressedTensorFunctional hB β π η hc ξ v (minimalElementary b c) =
      ⟪ξ, π (innerHomCompression β v b) (η c ξ)⟫_ℂ := by
  rw [compressedTensorFunctional, nuclearTensorFunctional_elementary,
    representedCompression_apply]
  rfl

lemma inclusionTensorFunctional_elementary (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) (b : B) (c : C) :
    inclusionTensorFunctional hB β π η hc ξ (minimalElementary b c) =
      ⟪ξ, π (β b) (η c ξ)⟫_ℂ := by
  simp only [inclusionTensorFunctional, nuclearTensorFunctional_elementary,
    innerHomCompression_apply, star_one, one_mul, mul_one,
    NonUnitalStarAlgHom.comp_apply]

lemma tensor_square_eq_of_compression_fixing (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] D)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) (v : D) (b : B) (c : C)
    (hfix : innerHomCompression β v (star b * b) = β (star b * b)) :
    inclusionTensorFunctional hB β π η hc ξ
        (star (minimalElementary b c) * minimalElementary b c) =
      compressedTensorFunctional hB β π η hc ξ v
        (star (minimalElementary b c) * minimalElementary b c) := by
  rw [← minimalElementary_star, ← minimalElementary_mul,
    inclusionTensorFunctional_elementary, compressedTensorFunctional_elementary, hfix]

variable {A : Type*} [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace B]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem abelian_compression_tensor_square_witness (hP : MainGap.PropertyP A)
    (hB : Nuclear B) (β : B →⋆ₙₐ[ℂ] N)
    (π : N →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) (b : B) (c : C) :
    ∃ v : N, ‖v‖ ≤ 1 ∧
      (∀ x y, Commute (innerHomCompression β v x) (innerHomCompression β v y)) ∧
      inclusionTensorFunctional hB β π η hc ξ
          (star (minimalElementary b c) * minimalElementary b c) =
        compressedTensorFunctional hB β π η hc ξ v
          (star (minimalElementary b c) * minimalElementary b c) := by
  obtain ⟨v, hv, hfix, hab⟩ :=
    abelian_range_compression_fixing_positive U hP β (star b * b) (star_mul_self_nonneg b)
  exact ⟨v, hv, hab, tensor_square_eq_of_compression_fixing hB β π η hc ξ v b c hfix⟩

end WeakPureInfiniteness

end

end OAI
