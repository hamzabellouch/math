import OAI.Analysis.KadisonSimilarity.Tracial.TracialIncludedCorners
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialHomCompression
import OAI.Analysis.KadisonSimilarity.Tracial.PopaConjugatePosition

namespace OAI

/-! Commutation and small-corner estimates pass to the concrete free copy
inside the prescribed subfactor ultrapower. Recovery of the original
commutator uses the exact constant GNS embedding. -/

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
local notation "τQ" => quotientTrace τB hB ω trB
local notation "G" => gnsTracialGeometry τQ (quotientTrace_tracial τB hB ω trB)

/-- An operator commuting with the original subfactor commutes with its
entire included ultrapower after the actual Hilbert compression. -/
theorem tracialUltrapowerCompression_commutes_range
    (T : τB.GNS →L[ℂ] τB.GNS)
    (hcomm : ∀ a, T.comp (τB.gnsStarAlgHom (φ a)) =
      (τB.gnsStarAlgHom (φ a)).comp T) :
    ∀ x : (Φ).range,
      (tracialUltrapowerCompression τB hB ω trB T).comp ((τQ).gnsStarAlgHom (x : _)) =
        ((τQ).gnsStarAlgHom (x : _)).comp (tracialUltrapowerCompression τB hB ω trB T) := by
  rintro ⟨_, a, rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (tracialUltrapowerCompression τB hB ω trB T).comp
    ((τQ).gnsStarAlgHom (Φ (quotientHom τA hA ω trA x))) =
    ((τQ).gnsStarAlgHom (Φ (quotientHom τA hA ω trA x))).comp
      (tracialUltrapowerCompression τB hB ω trB T)
  rw [tracialUltrapowerMap_mk]
  have hb := norm_tracialUltrapowerCompression_commutator_le τB hB ω trB T
    (boundedSequenceStarHom φ x) (c := 0) le_rfl
    (Filter.Eventually.of_forall (fun i => by
      have hz : commutator T (τB.gnsStarAlgHom (φ (x i))) = 0 := sub_eq_zero.mpr (hcomm (x i))
      change ‖commutator T (τB.gnsStarAlgHom (φ (x i)))‖ ≤ 0
      rw [hz, norm_zero]))
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)

/-- Every smaller subalgebra of the included ultrapower inherits commutation. -/
theorem tracialUltrapowerCompression_commutes_subalgebra
    (D : StarSubalgebra ℂ (Ultrapower τB hB ω trB)) (hD : D ≤ (Φ).range)
    (T : τB.GNS →L[ℂ] τB.GNS)
    (hcomm : ∀ a, T.comp (τB.gnsStarAlgHom (φ a)) =
      (τB.gnsStarAlgHom (φ a)).comp T) :
    ∀ x : D,
      (tracialUltrapowerCompression τB hB ω trB T).comp ((τQ).gnsStarAlgHom (x : _)) =
        ((τQ).gnsStarAlgHom (x : _)).comp (tracialUltrapowerCompression τB hB ω trB T) :=
  fun x => tracialUltrapowerCompression_commutes_range τA τB hA hB ω trA trB φ hφ
    T hcomm ⟨x, hD x.property⟩

/-- The exact strict trace gap gives the small-corner predicate consumed
by the original free-corner theorem on any contained free subfactor. -/
theorem included_ultrapower_traceCornerBound
    (rounding : SpectralProjectionRoundingInput τA)
    (D : StarSubalgebra ℂ (Ultrapower τB hB ω trB)) (hD : D ≤ (Φ).range)
    (T : τB.GNS →L[ℂ] τB.GNS) {ε s t : ℝ} (hε : 0 ≤ ε) (hts : t < s)
    (hcorner : ∀ (q : A) (hq : IsStarProjection q), (τA q).re ≤ s →
      ∀ z : CStarCorner (φ q) (hq.map φ),
        ‖commutator T (τB.gnsStarAlgHom (z : B))‖ ≤ ε * ‖z‖) :
    (G).TraceCornerBound D (tracialUltrapowerCompression τB hB ω trB T) t ε := by
  intro e he heD hte z
  obtain ⟨a, ha⟩ := hD heD
  subst e
  change IsStarProjection (Φ a) at he
  change (G).trace (Φ a) = (t : ℂ) at hte
  change CStarCorner (Φ a) he at z
  have hi := tracialUltrapowerMap_injective τA τB hA hB ω trA trB φ hφ
  have hp : IsStarProjection a := by
    constructor
    · apply hi
      simpa only [map_mul] using he.isIdempotentElem.eq
    · apply hi
      simpa only [map_star] using he.isSelfAdjoint.star_eq
  have ht : (quotientTrace τA hA ω trA a).re < s := by
    rw [← tracialUltrapowerMap_trace τA τB hA hB ω trA trB φ hφ]
    change ((G).trace (Φ a)).re < s
    rw [hte, Complex.ofReal_re]
    exact hts
  exact included_ultrapower_corner_bound τA τB hA hB ω trA trB φ hφ
    rounding T hε hcorner a hp ht z

/-- The final constant-subspace compression recovers the original
commutator with no loss in its norm bound. -/
theorem norm_commutator_le_ultrapower_constant_compression
    (T : τB.GNS →L[ℂ] τB.GNS) (b : B) :
    ‖commutator T (τB.gnsStarAlgHom b)‖ ≤
      ‖(G).baseOperator (constant τB hB ω trB).range
        (commutator (tracialUltrapowerCompression τB hB ω trB T)
          ((τQ).gnsStarAlgHom (constant τB hB ω trB b)))‖ :=
  norm_commutator_le_tracial_range_compression τB τQ
    (quotientTrace_tracial τB hB ω trB) (constant τB hB ω trB)
    (quotientTrace_constant τB hB ω trB) T (tracialUltrapowerCompression τB hB ω trB T)
    (constant_compression_tracialUltrapower τB hB ω trB T) b

end KadisonSimilarity

end

end OAI
