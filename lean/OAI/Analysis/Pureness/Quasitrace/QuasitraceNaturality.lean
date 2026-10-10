import OAI.Analysis.Pureness.Quasitrace.QuasitraceComplex

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder ComplexStarModule
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

def starHomSelfAdjointMap (φ : D →⋆ₙₐ[ℂ] E) : selfAdjoint D →ₗ[ℝ] selfAdjoint E where
  toFun a := ⟨φ a.1, by change star (φ a.1) = φ a.1; rw [← map_star,a.2.star_eq]⟩
  map_add' a b := Subtype.ext (map_add φ a.1 b.1)
  map_smul' r a := by
    apply Subtype.ext
    change φ (r • a.1) = r • φ a.1
    simpa only [← Complex.coe_smul] using map_smul φ (r : ℂ) a.1

lemma positiveMap_posPart (φ : D →⋆ₙₐ[ℂ] E) (a : selfAdjoint D) :
    Positive.map φ ⟨a.1⁺,CFC.posPart_nonneg _⟩ =
      ⟨(φ a.1)⁺,CFC.posPart_nonneg _⟩ := by
  apply Subtype.ext
  exact φ.map_cfcₙ (·⁺ : ℝ → ℝ) a.1 (by fun_prop) (by simp)
    (starHom_continuous φ) a.2 (starHomSelfAdjointMap φ a).2

lemma positiveMap_negPart (φ : D →⋆ₙₐ[ℂ] E) (a : selfAdjoint D) :
    Positive.map φ ⟨a.1⁻,CFC.negPart_nonneg _⟩ =
      ⟨(φ a.1)⁻,CFC.negPart_nonneg _⟩ := by
  apply Subtype.ext
  exact φ.map_cfcₙ (·⁻ : ℝ → ℝ) a.1 (by fun_prop) (by simp)
    (starHom_continuous φ) a.2 (starHomSelfAdjointMap φ a).2

namespace PositiveQuasitrace
variable (T : PositiveQuasitrace E) (U : PositiveQuasitrace D)

lemma selfAdjointValue_map (φ : D →⋆ₙₐ[ℂ] E)
    (h : ∀ a, T (Positive.map φ a) = U a) (a : selfAdjoint D) :
    T.selfAdjointValue (starHomSelfAdjointMap φ a) = U.selfAdjointValue a := by
  change T ⟨(φ a.1)⁺,_⟩-T ⟨(φ a.1)⁻,_⟩ = U ⟨a.1⁺,_⟩-U ⟨a.1⁻,_⟩
  rw [← positiveMap_posPart φ a,← positiveMap_negPart φ a,h,h]

theorem complexValue_map (φ : D →⋆ₙₐ[ℂ] E)
    (h : ∀ a, T (Positive.map φ a) = U a) (x : D) :
    T.complexValue (φ x) = U.complexValue x := by
  have hr : ℜ (φ x) = starHomSelfAdjointMap φ (ℜ x) := Subtype.ext (map_realPart φ x).symm
  have hi : ℑ (φ x) = starHomSelfAdjointMap φ (ℑ x) := Subtype.ext (map_imaginaryPart φ x).symm
  unfold complexValue
  rw [hr,hi,T.selfAdjointValue_map U φ h,T.selfAdjointValue_map U φ h]
end PositiveQuasitrace
end CuntzPureness

end

end OAI
