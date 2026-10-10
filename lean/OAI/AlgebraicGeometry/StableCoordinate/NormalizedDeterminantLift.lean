import OAI.AlgebraicGeometry.StableCoordinate.DeterminantUFD
import OAI.AlgebraicGeometry.StableCoordinate.QuadricFactorization
import OAI.AlgebraicGeometry.StableCoordinate.FrameQuotientMap
import OAI.AlgebraicGeometry.StableCoordinate.PolynomialFrameNormalization
import OAI.AlgebraicGeometry.StableCoordinate.CoactionLND

namespace OAI

/-!
# Constructing the normalized polynomial lift on the determinant ring

For every actual polynomial additive action on the exact quadric ring `B`,
this file constructs a polynomial family of algebra maps on the exact
`C = k[a,d,b,c,u]/(ac-bd-1)`.  Its restriction is the given action on `B`,
and its parameter-zero specialization is the identity on all of `C`.

Existence uses the proved UFD structure on `C[T]`, the concrete gcd frame
factorization, and normalization by a constant comparison unit.  No line
bundle, arbitrary frame, or lift-existence premise is assumed.  The additive
group law for this normalized family is proved separately by frame uniqueness.
-/

noncomputable section

namespace StableCoordinate.NormalizedDeterminantLift

open Obstruction FrameLift CoactionLND
open Polynomial

variable {k : Type*} [Field k]

/-- Pull the base action back along the actual quadric-to-determinant-ring map. -/
def pulledBase (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    Obstruction.B k →ₐ[k] Polynomial (Obstruction.C k) :=
  (Polynomial.mapAlgHom (sourceBaseMap k)).comp α.toAlgHom

@[simp] theorem pulledBase_apply (α : PolynomialAdditiveAction k (Obstruction.B k))
    (b : Obstruction.B k) :
    pulledBase α b = (α.toAlgHom b).map (sourceBaseMap k).toRingHom := rfl

@[simp] theorem pulledBase_at_zero (α : PolynomialAdditiveAction k (Obstruction.B k))
    (b : Obstruction.B k) :
    Polynomial.constantCoeff (pulledBase α b) = sourceBaseMap k b := by
  change (pulledBase α b).coeff 0 = _
  rw [pulledBase_apply, Polynomial.coeff_map, α.identity]
  rfl

/-- The polynomial base coordinates satisfy the quadric equation identically. -/
theorem pulledBase_relation (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    pulledBase α (bX k 0) * pulledBase α (bX k 1) =
      pulledBase α (bX k 2) * (pulledBase α (bX k 2) + 1) := by
  simpa only [map_mul, map_add, map_one] using
    congrArg (pulledBase α) (sub_eq_zero.mp (b_relation k))

/-- A genuine polynomial determinant frame exists by unique factorization. -/
def rawFrame (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    Frame (Polynomial (Obstruction.C k)) :=
  QuadricFactorization.frameAbove (pulledBase α (bX k 0))
    (pulledBase α (bX k 1)) (pulledBase α (bX k 2)) (pulledBase_relation α)

@[simp] theorem rawFrame_ab (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    (rawFrame α).a * (rawFrame α).b = pulledBase α (bX k 0) :=
  QuadricFactorization.frameAbove_ab _ _ _ _

@[simp] theorem rawFrame_dc (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    (rawFrame α).d * (rawFrame α).c = pulledBase α (bX k 1) :=
  QuadricFactorization.frameAbove_dc _ _ _ _

@[simp] theorem rawFrame_db (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    (rawFrame α).d * (rawFrame α).b = pulledBase α (bX k 2) :=
  QuadricFactorization.frameAbove_db _ _ _ _

/-- At parameter zero the raw frame and the original frame have the same base. -/
theorem rawFrame_at_zero_sameBase (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    SameBase ((rawFrame α).map Polynomial.constantCoeff) (sourceFrame k) := by
  constructor
  · change Polynomial.constantCoeff (rawFrame α).a *
      Polynomial.constantCoeff (rawFrame α).b = cX k 0 * cX k 2
    rw [← map_mul, rawFrame_ab, pulledBase_at_zero]
    simp
  constructor
  · change Polynomial.constantCoeff (rawFrame α).d *
      Polynomial.constantCoeff (rawFrame α).c = cX k 1 * cX k 3
    rw [← map_mul, rawFrame_dc, pulledBase_at_zero]
    simp
  · change Polynomial.constantCoeff (rawFrame α).d *
      Polynomial.constantCoeff (rawFrame α).b = cX k 1 * cX k 2
    rw [← map_mul, rawFrame_db, pulledBase_at_zero]
    simp

/-- The chosen polynomial frame has exactly the original frame at parameter zero. -/
def normalizedFrame (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    Frame (Polynomial (Obstruction.C k)) :=
  normalizePolynomialFrame (rawFrame α) (sourceFrame k) (rawFrame_at_zero_sameBase α)

theorem normalizedFrame_sameBase (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    SameBase (normalizedFrame α) (rawFrame α) :=
  normalizePolynomialFrame_sameBase _ _ _

@[simp] theorem normalizedFrame_at_zero (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    (normalizedFrame α).map Polynomial.constantCoeff = sourceFrame k :=
  normalizePolynomialFrame_at_zero _ _ _

@[simp] theorem normalizedFrame_ab (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    (normalizedFrame α).a * (normalizedFrame α).b = pulledBase α (bX k 0) :=
  (normalizedFrame_sameBase α).1.trans (rawFrame_ab α)

@[simp] theorem normalizedFrame_dc (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    (normalizedFrame α).d * (normalizedFrame α).c = pulledBase α (bX k 1) :=
  (normalizedFrame_sameBase α).2.1.trans (rawFrame_dc α)

@[simp] theorem normalizedFrame_db (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    (normalizedFrame α).d * (normalizedFrame α).b = pulledBase α (bX k 2) :=
  (normalizedFrame_sameBase α).2.2.trans (rawFrame_db α)

/-- The actual normalized polynomial-family homomorphism on the determinant ring.
The independent `u` coordinate is lifted through the same base action. -/
def liftHom (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    Obstruction.C k →ₐ[k] Polynomial (Obstruction.C k) :=
  (normalizedFrame α).quotientMap (pulledBase α (bX k 3))

/-- The family restricts to the original base action on the whole base algebra. -/
theorem liftHom_comp_baseMap (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    (liftHom α).comp (sourceBaseMap k) = pulledBase α :=
  Frame.quotientMap_comp_baseMap _ _ _ (normalizedFrame_ab α)
    (normalizedFrame_dc α) (normalizedFrame_db α) rfl

/-- Pointwise form of the exact base-extension identity. -/
theorem liftHom_baseMap (α : PolynomialAdditiveAction k (Obstruction.B k))
    (b : Obstruction.B k) :
    liftHom α (sourceBaseMap k b) = (α.toAlgHom b).map (sourceBaseMap k).toRingHom :=
  AlgHom.congr_fun (liftHom_comp_baseMap α) b

/-- Zero-parameter specialization, bundled as a coefficient-algebra homomorphism. -/
def atZero : Polynomial (Obstruction.C k) →ₐ[k] Obstruction.C k where
  toRingHom := Polynomial.constantCoeff
  commutes' r := by simp

/-- The normalization is an equality of actual algebra maps, not just of points. -/
theorem atZero_comp_liftHom (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    atZero.comp (liftHom α) = AlgHom.id k (Obstruction.C k) := by
  unfold liftHom
  rw [(normalizedFrame α).quotientMap_natural (pulledBase α (bX k 3)) (atZero (k := k))]
  change ((normalizedFrame α).map Polynomial.constantCoeff).quotientMap
    (Polynomial.constantCoeff (pulledBase α (bX k 3))) = _
  rw [normalizedFrame_at_zero, pulledBase_at_zero]
  simp

/-- The lifted polynomial family is normalized on every element of `C`. -/
@[simp] theorem liftHom_identity (α : PolynomialAdditiveAction k (Obstruction.B k))
    (c : Obstruction.C k) : (liftHom α c).coeff 0 = c :=
  AlgHom.congr_fun (atZero_comp_liftHom α) c

/-- Unconditional existence of a normalized polynomial lift over the exact rings. -/
theorem exists_normalized_lift (α : PolynomialAdditiveAction k (Obstruction.B k)) :
    ∃ β : Obstruction.C k →ₐ[k] Polynomial (Obstruction.C k),
      (∀ c, (β c).coeff 0 = c) ∧
      (∀ b, β (sourceBaseMap k b) = (α.toAlgHom b).map (sourceBaseMap k).toRingHom) :=
  ⟨liftHom α, liftHom_identity α, liftHom_baseMap α⟩

end StableCoordinate.NormalizedDeterminantLift

end

end OAI
