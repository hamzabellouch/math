import Mathlib
import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
import OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry

namespace PiExponent.CurveZeroEuler

def algebraStructureMap (B : Type) [CommRing B] [Algebra ℂ B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ B))

def specStructureSectionsEquiv (B : Type) [CommRing B] [Algebra ℂ B] :
    letI : Module ℂ Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) :=
      Module.compHom _ (baseScalars (algebraStructureMap B))
    Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) ≃ₗ[ℂ] B := by
  letI : Module ℂ Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) :=
    Module.compHom _ (baseScalars (algebraStructureMap B))
  refine { ((Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv).toAddEquiv with
    map_smul' := ?_ }
  intro c x
  change Γ(Spec (CommRingCat.of B), ⊤) at x
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    (baseScalars (algebraStructureMap B) c * x) =
      c • (Scheme.ΓSpecIso (CommRingCat.of B)).hom x
  rw [Algebra.smul_def]
  rw [map_mul]
  congr 1
  change ((Spec.map (CommRingCat.ofHom (algebraMap ℂ B))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) = _
  rw [Scheme.ΓSpecIso_naturality]
  simp

theorem affine_algebra_eulerCharacteristic (B : Type) [CommRing B] [Algebra ℂ B]
    [IsNoetherianRing B] (d : ℕ) :
    eulerCharacteristic (algebraStructureMap B) d
      (structureSheaf (Spec (CommRingCat.of B))) = (Module.finrank ℂ B : ℤ) := by
  let : (structureSheaf (Spec (CommRingCat.of B))).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr (by
      change IsIso (Scheme.Modules.fromTildeΓ (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      infer_instance)
  rw [affine_eulerCharacteristic]
  let : Module ℂ Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) :=
    Module.compHom _ (baseScalars (algebraStructureMap B))
  exact congrArg (fun n : ℕ => (n : ℤ)) (specStructureSectionsEquiv B).finrank_eq

theorem principal_zero_euler_eq_order
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    {a : A} (ha : a ≠ 0) (d : ℕ) :
    eulerCharacteristic (algebraStructureMap (A ⧸ Ideal.span {a})) d
      (structureSheaf (Spec (CommRingCat.of (A ⧸ Ideal.span {a})))) =
        ((IsDiscreteValuationRing.addVal A a).toNat : ℤ) := by
  rw [affine_algebra_eulerCharacteristic]
  have h := CurveLocalOrder.principal_quotient_finrank_eq_order_of_algClosed (F := ℂ) ha
  rw [← h]
  simp

theorem rational_order_eq_euler_difference
    {A K : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) (d : ℕ) :
    WeightedCurveDegree.integerOrder (CurveLocalOrder.fractionAddValuation A K)
      (Units.mk0 (algebraMap A K a)
        ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha) /
       Units.mk0 (algebraMap A K b)
        ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb)) =
      eulerCharacteristic (algebraStructureMap (A ⧸ Ideal.span {a})) d
        (structureSheaf (Spec (CommRingCat.of (A ⧸ Ideal.span {a})))) -
      eulerCharacteristic (algebraStructureMap (A ⧸ Ideal.span {b})) d
        (structureSheaf (Spec (CommRingCat.of (A ⧸ Ideal.span {b})))) := by
  rw [WeightedCurveDegree.integerOrder_div,
    CurveLocalOrder.integerOrder_field_image_eq_length ha,
    CurveLocalOrder.integerOrder_field_image_eq_length hb,
    principal_zero_euler_eq_order ha, principal_zero_euler_eq_order hb,
    CurveLocalOrder.length_quotient_span_eq_addVal ha,
    CurveLocalOrder.length_quotient_span_eq_addVal hb]

end PiExponent.CurveZeroEuler

end

end OAI
