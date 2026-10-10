import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerHom
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeDihedral
import OAI.Analysis.KadisonSimilarity.Tracial.TracialEmbeddingTransport
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! The conjugacy form of Popa's free-position construction: a unitary in
an irreducibly included subfactor's tracial ultrapower conjugates a prescribed
constant subfactor to a copy free from the ambient constant algebra.
The conjugating unitary remains in the prescribed subfactor ultrapower, and
trace preservation transports the matrix presentation to its conjugated copy.
-/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

/-- The prescribed subfactor is embedded as constants, conjugated inside A^ω,
then included in B^ω. Thus membership in the prescribed ultrapower is retained. -/
def conjugatedConstantEmbedding (ρ : R →⋆ₐ[ℂ] A)
    (u : unitary (Ultrapower τA hA ω trA)) : R →⋆ₐ[ℂ] Ultrapower τB hB ω trB :=
  (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ).comp
    ((Unitary.conjStarAlgAut ℂ (Ultrapower τA hA ω trA) u).toStarAlgHom.comp
      ((constant τA hA ω trA).comp ρ))

/-- Local published specialization for a fixed irreducible inclusion of
separable II₁ factors A⊂B and a fixed separable subfactor ρ(R)⊂A.
The two free algebras are concrete ranges, rather than unspecified copies. -/
def Popa1995ConjugateFreenessInput
    (_hω : (ω : Filter ℕ) ≤ Filter.cofinite) (ρ : R →⋆ₐ[ℂ] A) : Prop :=
  ∃ u : unitary (Ultrapower τA hA ω trA),
    ScalarFree (quotientTrace τB hB ω trB).toLinearMap
      (constant τB hB ω trB).range
      (conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u).range

theorem quotientTrace_unitary_conjugate (u : unitary (Ultrapower τA hA ω trA))
    (x : Ultrapower τA hA ω trA) :
    quotientTrace τA hA ω trA
      (Unitary.conjStarAlgAut ℂ (Ultrapower τA hA ω trA) u x) =
        quotientTrace τA hA ω trA x := by
  change quotientTrace τA hA ω trA ((u : Ultrapower τA hA ω trA) * x * star (u : Ultrapower τA hA ω trA)) = _
  rw [quotientTrace_tracial τA hA ω trA,
    ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

/-- The conjugated constant copy has exactly its original trace. -/
theorem conjugatedConstantEmbedding_trace (ρ : R →⋆ₐ[ℂ] A)
    (u : unitary (Ultrapower τA hA ω trA)) (x : R) :
    quotientTrace τB hB ω trB
      (conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u x) = τA (ρ x) := by
  change quotientTrace τB hB ω trB
    (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ
      (Unitary.conjStarAlgAut ℂ (Ultrapower τA hA ω trA) u
        (constant τA hA ω trA (ρ x)))) = _
  rw [tracialUltrapowerMap_trace, quotientTrace_unitary_conjugate, quotientTrace_constant]

/-- Its range lies inside the included A-ultrapower, as required by the
coordinate small-corner transfer. -/
theorem conjugatedConstantEmbedding_range_le (ρ : R →⋆ₐ[ℂ] A)
    (u : unitary (Ultrapower τA hA ω trA)) :
    (conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u).range ≤
      (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ).range := by
  rintro x ⟨y, rfl⟩
  exact ⟨_, rfl⟩

/-- Faithfulness survives the constant embedding, conjugation, and inclusion. -/
theorem conjugatedConstantEmbedding_injective (ρ : R →⋆ₐ[ℂ] A)
    (hρ : Function.Injective ρ)
    (hfA : ∀ a : A, τA (star a * a) = 0 → a = 0)
    (u : unitary (Ultrapower τA hA ω trA)) :
    Function.Injective (conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u) :=
  (tracialUltrapowerMap_injective τA τB hA hB ω trA trB φ hφ).comp
    ((Unitary.conjStarAlgAut ℂ (Ultrapower τA hA ω trA) u).injective.comp
      ((constant_injective τA hA ω trA hfA).comp hρ))

/-- An embedded C-star algebra has closed range; this supplies the actual
closed subalgebra used for the matrix-tower transport. -/
theorem conjugatedConstantEmbedding_range_isClosed (ρ : R →⋆ₐ[ℂ] A)
    (hρ : Function.Injective ρ)
    (hfA : ∀ a : A, τA (star a * a) = 0 → a = 0)
    (u : unitary (Ultrapower τA hA ω trA)) :
    IsClosed ((conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u).range :
      Set (Ultrapower τB hB ω trB)) :=
  (NonUnitalStarAlgHom.isometry _
    (conjugatedConstantEmbedding_injective τA τB hA hB ω trA trB φ hφ ρ hρ hfA u)).isClosedEmbedding.isClosed_range

end KadisonSimilarity

end

end OAI
