import OAI.AlgebraicGeometry.StableCoordinate.CoactionBaseNaturality
import OAI.AlgebraicGeometry.StableCoordinate.FrameCoassociativity
import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import OAI.AlgebraicGeometry.StableCoordinate.BundleCharts

namespace OAI

/-!
# The action law for a normalized lift to the determinant algebra

The polynomial family constructed from a normalized determinant frame is not
assumed to be an action.  This file proves its additive group law from that of
the base family, using the uniqueness of normalized frames.
-/

noncomputable section
namespace StableCoordinate.FrameLiftCoassoc

open Polynomial
open CoactionLND

variable {k B A : Type*} [CommRing k] [CommRing B] [CommRing A]
  [Algebra k B] [Algebra k A]

/-- Applying the lifted family twice, with two independent parameters. -/
def iterateMap (β : A →ₐ[k] A[X]) : A →ₐ[k] A[X][X] :=
  (Polynomial.mapAlgHom β).comp β

/-- Applying the lifted family at the sum of two independent parameters. -/
def sumParameterMap (β : A →ₐ[k] A[X]) : A →ₐ[k] A[X][X] :=
  ((Polynomial.taylorAlgHom (X : A[X])).restrictScalars k).comp
    ((Polynomial.mapAlgHom (Polynomial.CAlgHom : A →ₐ[k] A[X])).comp β)

@[simp] theorem iterateMap_apply (β : A →ₐ[k] A[X]) (r : A) :
    iterateMap β r = (β r).map β.toRingHom := rfl

@[simp] theorem sumParameterMap_apply (β : A →ₐ[k] A[X]) (r : A) :
    sumParameterMap β r =
      taylor (X : A[X]) ((β r).map (C : A →+* A[X])) := rfl

/-- Equality of the two action-law maps can be tested on the five actual
quotient generators, and not merely on their values at complex points. -/
theorem coassoc_of_generators
    (β : Obstruction.C k →ₐ[k] (Obstruction.C k)[X])
    (h : ∀ i : Fin 5,
      (β (Obstruction.cX k i)).map β.toRingHom =
        taylor (X : (Obstruction.C k)[X])
          ((β (Obstruction.cX k i)).map (C : Obstruction.C k →+* (Obstruction.C k)[X]))) :
    ∀ r, (β r).map β.toRingHom =
      taylor (X : (Obstruction.C k)[X]) ((β r).map (C : Obstruction.C k →+* (Obstruction.C k)[X])) := by
  have heq : iterateMap β = sumParameterMap β := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change iterateMap β (Obstruction.cX k i) = sumParameterMap β (Obstruction.cX k i)
    exact h i
  intro r
  exact AlgHom.congr_fun heq r

/-- A normalized family on the actual determinant quotient extending a base
additive action automatically satisfies the complete bivariate action law. -/
theorem coassoc_of_normalized_extension
    [IsReduced (Obstruction.C k)]
    (α : PolynomialAdditiveAction k (Obstruction.B k))
    (β : Obstruction.C k →ₐ[k] (Obstruction.C k)[X])
    (hidentity : ∀ r, (β r).coeff 0 = r)
    (hbase : ∀ b, β (BundleCharts.baseMap k b) =
      (α.toAlgHom b).map (BundleCharts.baseMap k).toRingHom) :
    ∀ r, (β r).map β.toRingHom =
      taylor (X : (Obstruction.C k)[X])
        ((β r).map (C : Obstruction.C k →+* (Obstruction.C k)[X])) := by
  let F : FrameLift.Frame (Obstruction.C k) :=
    ⟨Obstruction.cX k 0, Obstruction.cX k 1,
      Obstruction.cX k 2, Obstruction.cX k 3,
      sub_eq_zero.mp (Obstruction.c_relation k)⟩
  have hcoord (i : Fin 4) : FrameLift.CoassociativeAt β.toRingHom
      (BundleCharts.baseMap k (Obstruction.bX k i)) :=
    coassoc_on_image_of_extension α β (BundleCharts.baseMap k) hbase (Obstruction.bX k i)
  have hx : BundleCharts.baseMap k (Obstruction.bX k 0) =
      Obstruction.cX k 0 * Obstruction.cX k 2 := by
    change BundleCharts.baseMap k (BundleCharts.qgen k 0) = BundleCharts.dgen k 0 * BundleCharts.dgen k 2
    exact BundleCharts.baseMap_qgen k 0
  have hy : BundleCharts.baseMap k (Obstruction.bX k 1) =
      Obstruction.cX k 1 * Obstruction.cX k 3 := by
    change BundleCharts.baseMap k (BundleCharts.qgen k 1) = BundleCharts.dgen k 1 * BundleCharts.dgen k 3
    exact BundleCharts.baseMap_qgen k 1
  have hz : BundleCharts.baseMap k (Obstruction.bX k 2) =
      Obstruction.cX k 1 * Obstruction.cX k 2 := by
    change BundleCharts.baseMap k (BundleCharts.qgen k 2) = BundleCharts.dgen k 1 * BundleCharts.dgen k 2
    exact BundleCharts.baseMap_qgen k 2
  have hu : BundleCharts.baseMap k (Obstruction.bX k 3) =
      Obstruction.cX k 4 := by
    change BundleCharts.baseMap k (BundleCharts.qgen k 3) = BundleCharts.dgen k 4
    exact BundleCharts.baseMap_qgen k 3
  have hab : FrameLift.CoassociativeAt β.toRingHom (F.a * F.b) := by
    simpa only [hx] using hcoord 0
  have hdc : FrameLift.CoassociativeAt β.toRingHom (F.d * F.c) := by
    simpa only [hy] using hcoord 1
  have hdb : FrameLift.CoassociativeAt β.toRingHom (F.d * F.b) := by
    simpa only [hz] using hcoord 2
  have hF := FrameLift.coassociative_on_frame_entries β.toRingHom hidentity F
    ⟨hab, hdc, hdb⟩
  apply coassoc_of_generators β
  intro i
  fin_cases i
  · exact hF.1
  · exact hF.2.1
  · exact hF.2.2.1
  · exact hF.2.2.2
  · change FrameLift.CoassociativeAt β.toRingHom (Obstruction.cX k 4)
    simpa only [hu] using hcoord 3

/-- Construct the genuine additive action from a normalized extending family.
The family is supplied by the separately proved determinant-frame construction;
its group law is proved here, not taken as an assumption. -/
def actionOfNormalizedExtension
    [IsReduced (Obstruction.C k)]
    (α : PolynomialAdditiveAction k (Obstruction.B k))
    (β : Obstruction.C k →ₐ[k] (Obstruction.C k)[X])
    (hidentity : ∀ r, (β r).coeff 0 = r)
    (hbase : ∀ b, β (BundleCharts.baseMap k b) =
      (α.toAlgHom b).map (BundleCharts.baseMap k).toRingHom) :
    PolynomialAdditiveAction k (Obstruction.C k) where
  toAlgHom := β
  identity := hidentity
  coassoc := coassoc_of_normalized_extension α β hidentity hbase

@[simp] theorem actionOfNormalizedExtension_toAlgHom
    [IsReduced (Obstruction.C k)]
    (α : PolynomialAdditiveAction k (Obstruction.B k))
    (β : Obstruction.C k →ₐ[k] (Obstruction.C k)[X])
    (hidentity : ∀ r, (β r).coeff 0 = r)
    (hbase : ∀ b, β (BundleCharts.baseMap k b) =
      (α.toAlgHom b).map (BundleCharts.baseMap k).toRingHom) :
    (actionOfNormalizedExtension α β hidentity hbase).toAlgHom = β := rfl

end StableCoordinate.FrameLiftCoassoc

end

end OAI
