import OAI.Analysis.BoundedHochschild.CornerEquivalences

namespace OAI

/-!
# Equivalence of corners joined by a partial isometry

Conjugation by a partial isometry identifies its initial and final corners as
actual star algebras. In particular abelianness passes between these corners
and to smaller projections.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- Conjugation identifies the initial and final corners of a partial isometry. -/
def partialIsoCornerEquiv (v : PartialIso M) :
    PopaCorner.algebra v.initial_proj ≃⋆ₐ[ℂ] PopaCorner.algebra v.final_proj where
  toFun a := ⟨(v : M) * (a : M) * star (v : M), by
    constructor
    · rw [← mul_assoc, ← mul_assoc, v.final_mul]
    · have hs : star (v : M) * v.final = star (v : M) := by
        simpa only [star_mul, star_star, v.final_proj.isSelfAdjoint.star_eq] using
          congrArg star v.final_mul
      change ((v : M) * (a : M) * star (v : M)) * v.final = _
      rw [mul_assoc, hs]⟩
  invFun b := ⟨star (v : M) * (b : M) * (v : M), by
    constructor
    · have hs : v.initial * star (v : M) = star (v : M) := by
        simpa only [star_mul, star_star, v.initial_proj.isSelfAdjoint.star_eq] using
          congrArg star v.mul_initial
      change v.initial * (star (v : M) * (b : M) * (v : M)) = _
      rw [← mul_assoc, ← mul_assoc, hs]
    · rw [mul_assoc, v.mul_initial]⟩
  left_inv a := by
    apply Subtype.ext
    change star (v : M) * ((v : M) * (a : M) * star (v : M)) * (v : M) = (a : M)
    calc
      _ = v.initial * (a : M) * v.initial := by simp only [PartialIso.initial, mul_assoc]
      _ = (a : M) := by rw [a.property.1, a.property.2]
  right_inv b := by
    apply Subtype.ext
    change (v : M) * (star (v : M) * (b : M) * (v : M)) * star (v : M) = (b : M)
    calc
      _ = v.final * (b : M) * v.final := by simp only [PartialIso.final, mul_assoc]
      _ = (b : M) := by rw [b.property.1, b.property.2]
  map_add' a b := by
    apply Subtype.ext
    change (v : M) * ((a : M) + (b : M)) * star (v : M) =
      (v : M) * (a : M) * star (v : M) + (v : M) * (b : M) * star (v : M)
    simp only [mul_add, add_mul]
  map_mul' a b := by
    apply Subtype.ext
    change (v : M) * ((a : M) * (b : M)) * star (v : M) =
      ((v : M) * (a : M) * star (v : M)) * ((v : M) * (b : M) * star (v : M))
    symm
    calc
      _ = (v : M) * ((a : M) * v.initial * (b : M)) * star (v : M) := by
        simp only [PartialIso.initial, mul_assoc]
      _ = _ := by rw [a.property.2]
  map_smul' c a := by
    apply Subtype.ext
    change (v : M) * (c • (a : M)) * star (v : M) =
      c • ((v : M) * (a : M) * star (v : M))
    simp only [mul_smul_comm, smul_mul_assoc]
  map_star' a := by
    apply Subtype.ext
    change (v : M) * star (a : M) * star (v : M) =
      star ((v : M) * (a : M) * star (v : M))
    simp only [star_mul, star_star, mul_assoc]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma partialIsoCornerEquiv_apply (v : PartialIso M)
    (a : PopaCorner.algebra v.initial_proj) :
    (partialIsoCornerEquiv v a : M) = (v : M) * (a : M) * star (v : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
/-- Equivalent projections have simultaneously abelian corners. -/
lemma abelianProjection_partialIso (v : PartialIso M)
    (hab : PopaTypeII.AbelianProjection v.initial_proj) :
    PopaTypeII.AbelianProjection v.final_proj := by
  let E := partialIsoCornerEquiv v
  intro a b
  simpa only [E.apply_symm_apply] using (hab (E.symm a) (E.symm b)).map E

/-- A subprojection of an abelian projection is abelian. -/
lemma abelian_projection_mono {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hqp : q ≤ p)
    (hab : PopaTypeII.AbelianProjection hp) : PopaTypeII.AbelianProjection hq := by
  let lift (a : PopaCorner.algebra hq) : PopaCorner.algebra hp := ⟨(a : M), by
    constructor
    · calc
        p * (a : M) = p * (q * (a : M)) := by rw [a.property.1]
        _ = (a : M) := by rw [← mul_assoc, (hq.le_iff_mul_eq_right hp).mp hqp,
          a.property.1]
    · calc
        (a : M) * p = ((a : M) * q) * p := by rw [a.property.2]
        _ = (a : M) := by rw [mul_assoc, (hq.le_iff_mul_eq_left hp).mp hqp,
          a.property.2]⟩
  intro a b
  apply Subtype.ext
  exact congrArg (fun c : PopaCorner.algebra hp => (c : M)) (hab (lift a) (lift b)).eq

end KadisonRingrose
end BoundedHochschild

end

end OAI
