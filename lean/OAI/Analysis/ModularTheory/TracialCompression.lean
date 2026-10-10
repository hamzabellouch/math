import OAI.Analysis.ModularTheory.TracialCorners

namespace OAI

/-! Compression of the actual left/right multiplication operators. The
joint projection need not commute with either factor separately. -/
noncomputable section
open MeasureTheory
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularTracialRightAction_mul (S : StandardModularData H)
    (a b : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    modularTracialRightAction S (a * b) =
      modularTracialRightAction S b * modularTracialRightAction S a := by
  change antiunitaryConjugate (modularTraceAntiunitary S) (star (a * b)) = _
  rw [star_mul, antiunitaryConjugate_mul _ (modularTraceAntiunitary_involutive S)]
  rfl

lemma modularTracialCornerProjection_compress (S : StandardModularData H) (n : ℕ)
    (a b : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S)
    (hb : b ∈ modularCrossedProduct volume S) :
    modularTracialCornerProjection S n * (a * modularTracialRightAction S b) *
        modularTracialCornerProjection S n =
      (modularFiniteProjection (H := H) n * a * modularFiniteProjection n) *
        modularTracialRightAction S
          (modularFiniteProjection (H := H) n * b * modularFiniteProjection n) := by
  let p := modularFiniteProjection (H := H) n
  let r := modularTracialRightAction S p
  let s := modularTracialRightAction S b
  have hpa : a * r = r * a :=
    modularTracialRightAction_commutes S a p ha (modularFiniteProjection_mem S n)
  have hpp : p * r = r * p :=
    modularTracialRightAction_commutes S p p (modularFiniteProjection_mem S n)
      (modularFiniteProjection_mem S n)
  have hbp : p * s = s * p :=
    modularTracialRightAction_commutes S p b (modularFiniteProjection_mem S n) hb
  have hr : modularTracialRightAction S (p * b * p) = r * s * r := by
    rw [modularTracialRightAction_mul, modularTracialRightAction_mul]
    exact (mul_assoc r s r).symm
  change (p * r) * (a * s) * (p * r) = (p * a * p) *
    modularTracialRightAction S (p * b * p)
  rw [hr]
  calc
    _ = p * (r * a) * (s * p) * r := by noncomm_ring
    _ = p * (a * r) * (p * s) * r := by rw [← hpa, ← hbp]
    _ = p * a * (r * p) * s * r := by noncomm_ring
    _ = p * a * (p * r) * s * r := by rw [← hpp]
    _ = _ := by noncomm_ring

end WeakPureInfiniteness

end

end OAI
