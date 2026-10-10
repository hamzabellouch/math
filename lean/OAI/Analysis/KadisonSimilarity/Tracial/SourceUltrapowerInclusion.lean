import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerHom
import OAI.Analysis.BoundedHochschild.UltrapowerMoments

namespace OAI

/-! Coordinate source unitaries define the required unitary in the actual
source ultrapower, and its ambient image is the coordinatewise image. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower HochschildPatching TracialUltrapower
open scoped ComplexOrder BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b, τA (a * b) = τA (b * a))
  (trB : ∀ a b, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (ht : ∀ a, τB (φ a) = τA a)

theorem tracialUltrapowerMap_quotientUnitary (u : ℕ → unitary A) :
    tracialUltrapowerMap τA τB hA hB ω trA trB φ ht
      (quotientUnitary τA hA ω trA u : Ultrapower τA hA ω trA) =
    (quotientUnitary τB hB ω trB (fun n => mapUnitary φ (u n)) :
      Ultrapower τB hB ω trB) := by
  rw [quotientUnitary_coe, tracialUltrapowerMap_mk, quotientUnitary_coe]
  congr 1
  ext n
  simp only [boundedSequenceStarHom_apply, unitarySequence_apply, mapUnitary_coe]

theorem mapUnitary_tracialUltrapowerMap (u : ℕ → unitary A) :
    mapUnitary (tracialUltrapowerMap τA τB hA hB ω trA trB φ ht)
      (quotientUnitary τA hA ω trA u) =
    quotientUnitary τB hB ω trB (fun n => mapUnitary φ (u n)) := by
  apply Subtype.ext
  exact tracialUltrapowerMap_quotientUnitary τA τB hA hB ω trA trB φ ht u

end KadisonSimilarity

end

end OAI
