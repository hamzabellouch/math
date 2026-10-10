import OAI.Analysis.KadisonSimilarity.Representation.PolarPartialIsometry
import OAI.Analysis.KadisonSimilarity.Representation.SpectralRoundingDischarge
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialPropagationEndgame

namespace OAI

/-! # Right support trace bounds from the constructed polar partial isometry -/
noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Trace comparison needs only traciality and positivity once the polar
partial isometry has been constructed. -/
theorem trace_initial_le_leftSupport {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (v q : A) (hq : IsStarProjection q) (hv : IsStarProjection (v * star v))
    (hqv : q * v = v) : (τ (star v * v)).re ≤ (τ q).re := by
  have hqs : q * (v * star v) = v * star v := by rw [← mul_assoc, hqv]
  have hpos := τ.map_nonneg (hv.sub_of_mul_eq_right hq hqs).nonneg
  change 0 ≤ τ (q - v * star v) at hpos
  have ht : τ (v * star v) = τ (star v * v) := htr _ _
  rw [map_sub, ht] at hpos
  exact sub_nonneg.mp (show 0 ≤ (τ q).re - (τ (star v * v)).re from hpos.1)

section Tracial
variable (P : VonNeumannAlgebra H)
local instance supportClosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed P.carrier
  rw [← P.centralizer_centralizer']
  exact Set.isClosed_centralizer _
local instance supportCStar : CStarAlgebra P.toStarSubalgebra := inferInstance
local instance supportOrder : PartialOrder P.toStarSubalgebra := inferInstance
local instance supportStarOrder : StarOrderedRing P.toStarSubalgebra := inferInstance

/-- The constructed right support has trace no larger than any containing
left support. No normality of the tracial positive functional is used. -/
theorem exists_rightSupport_trace_le
    (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (q x : P.toStarSubalgebra) (hq : IsStarProjection q) (hqx : q * x = x) :
    ∃ r : P.toStarSubalgebra, IsStarProjection r ∧ (τ r).re ≤ (τ q).re ∧ x * r = x := by
  let v : P.toStarSubalgebra :=
    ⟨polarPartialIsometry (x : H →L[ℂ] H), polarPartialIsometry_mem P x x.property⟩
  let r : P.toStarSubalgebra := ⟨rangeSupport (polarModulus (x : H →L[ℂ] H)),
    rangeSupport_mem P _ (polarModulus_mem P x x.property)⟩
  have hr : IsStarProjection r := by
    apply isStarProjection_subtype_of_coe
    change IsStarProjection (rangeSupport (polarModulus (x : H →L[ℂ] H)))
    exact rangeSupport_isStarProjection (H := H) (polarModulus (x : H →L[ℂ] H))
  have hv : IsStarProjection (v * star v) := by
    apply isStarProjection_subtype_of_coe
    change IsStarProjection (polarPartialIsometry (x : H →L[ℂ] H) *
      star (polarPartialIsometry (x : H →L[ℂ] H)))
    exact polarPartialIsometry_final (H := H) (x : H →L[ℂ] H)
  have hvr : star v * v = r := by
    apply Subtype.ext
    change star (polarPartialIsometry (x : H →L[ℂ] H)) * polarPartialIsometry (x : H →L[ℂ] H) =
      rangeSupport (polarModulus (x : H →L[ℂ] H))
    exact polarPartialIsometry_initial (H := H) (x : H →L[ℂ] H)
  have hqv : q * v = v := by
    apply Subtype.ext
    change (q : H →L[ℂ] H) * polarPartialIsometry (x : H →L[ℂ] H) =
      polarPartialIsometry (x : H →L[ℂ] H)
    exact leftSupport_polarPartialIsometry (H := H) (x : H →L[ℂ] H)
      (q : H →L[ℂ] H) (congrArg Subtype.val hqx)
  refine ⟨r, hr, ?_, ?_⟩
  · rw [← hvr]
    exact trace_initial_le_leftSupport τ htr v q hq hv hqv
  · apply Subtype.ext
    let X : H →L[ℂ] H := x
    change X * rangeSupport (polarModulus X) = X
    calc
      _ = (polarPartialIsometry X * polarModulus X) * rangeSupport (polarModulus X) := by
        rw [polarPartialIsometry_mul_modulus]
      _ = polarPartialIsometry X * (polarModulus X * rangeSupport (polarModulus X)) :=
        mul_assoc _ _ _
      _ = X := by rw [mul_rangeSupport _ (polarModulus_selfAdjoint X),
        polarPartialIsometry_mul_modulus]

/-- Discharge of the exact support input used in propagation. -/
theorem tracialRightSupportInput
    (τ : P.toStarSubalgebra →ₚ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (q : P.toStarSubalgebra) (hq : IsStarProjection q)
    (A : StarSubalgebra ℂ P.toStarSubalgebra) :
    TracialRightSupportInput (fun a => (τ a).re) q A := by
  intro a
  apply exists_rightSupport_trace_le P τ htr q (q * (a : P.toStarSubalgebra)) hq
  rw [← mul_assoc, hq.isIdempotentElem.eq]

end Tracial

end KadisonSimilarity

end

end OAI
