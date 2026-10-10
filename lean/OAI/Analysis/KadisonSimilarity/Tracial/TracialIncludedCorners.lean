import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerCorners
import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerHom

namespace OAI

/-! Small-corner bounds from Q inside P pass to the included tracial
ultrapower Q^ω inside P^ω. The strict trace gap is explicit. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "Φ" => tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ

/-- The full small-corner transfer, including lifting inside the prescribed
subalgebra, near-minimal quotient lifts, and Hilbert compression. -/
theorem included_ultrapower_corner_bound
    (rounding : SpectralProjectionRoundingInput τA)
    (T : τB.GNS →L[ℂ] τB.GNS) {ε s : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ (q : A) (hq : IsStarProjection q), (τA q).re ≤ s →
      ∀ z : CStarCorner (φ q) (hq.map φ),
        ‖commutator T (τB.gnsStarAlgHom (z : B))‖ ≤ ε * ‖z‖)
    (e : Ultrapower τA hA ω trA) (he : IsStarProjection e)
    (hte : (quotientTrace τA hA ω trA e).re < s)
    (z : CStarCorner (Φ e) (he.map Φ)) :
    ‖commutator (tracialUltrapowerCompression τB hB ω trB T)
      ((quotientTrace τB hB ω trB).gnsStarAlgHom
        (z : Ultrapower τB hB ω trB))‖ ≤ ε * ‖z‖ := by
  obtain ⟨p, hp, hpt, hpe⟩ := exists_projection_representative_trace_le
    τA hA ω trA rounding e he hte
  let pB := boundedSequenceStarHom φ p
  have hpB (i : ℕ) : IsStarProjection (pB i) := (hp i).map φ
  have hpBe : quotientHom τB hB ω trB pB = Φ e := by
    rw [← hpe, tracialUltrapowerMap_mk]
  exact tracialUltrapower_corner_bound_of_projection_lift τB hB ω trB T pB hpB
    (Φ e) (he.map Φ) hpBe hε (fun i => hcorner (p i) (hp i) (hpt i)) z

end KadisonSimilarity

end

end OAI
