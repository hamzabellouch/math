import Mathlib
import OAI.NumberTheory.PiExponent.Cohomology.CurveZeroEuler
import OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
universe u

namespace PiExponent.LocalSectionOrder

def localCoefficient
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom (coefficient e s)

def localFrameChange
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A))) : Aˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (frameChange e f)

theorem localCoefficient_change
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) :
    localCoefficient f s = (localFrameChange e f : A) * localCoefficient e s := by
  unfold localCoefficient
  rw [coefficient_change e f s, map_mul]
  rfl

theorem zeroIdeal_frame_independent
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) :
    Ideal.span {localCoefficient e s} = Ideal.span {localCoefficient f s} := by
  rw [localCoefficient_change e f,
    Ideal.span_singleton_mul_left_unit (localFrameChange e f).isUnit]

def sectionOrder
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : ℕ∞ :=
  IsDiscreteValuationRing.addVal A (localCoefficient e s)

theorem sectionOrder_frame_independent
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) :
    sectionOrder e s = sectionOrder f s := by
  unfold sectionOrder
  rw [localCoefficient_change e f, AddValuation.map_mul,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]

theorem localCoefficient_eq_zero_iff
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : localCoefficient e s = 0 ↔ s = 0 := by
  constructor
  · intro h
    have hc : coefficient e s = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
      simpa only [localCoefficient, map_zero] using h
    have he : s ≫ e.hom = 0 := by
      ext U a
      change Γ(Spec (CommRingCat.of A), U) at a
      change (s ≫ e.hom).app U a = (0 : Γ(Spec (CommRingCat.of A), U))
      rw [end_apply, end_naturality]
      change a * (Spec (CommRingCat.of A)).presheaf.map _ (coefficient e s) = 0
      rw [hc, map_zero]
      exact mul_zero a
    apply (cancel_mono e.hom).mp
    simpa using he
  · intro h
    subst h
    unfold localCoefficient coefficient endValue
    rw [zero_comp]
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom (0 : Γ(Spec (CommRingCat.of A), ⊤)) = 0
    exact map_zero _

def zeroScheme
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : Scheme :=
  Spec (CommRingCat.of (A ⧸ Ideal.span {localCoefficient e s}))

theorem zeroScheme_frame_independent
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : zeroScheme e s = zeroScheme f s := by
  unfold zeroScheme
  rw [zeroIdeal_frame_independent e f]

theorem zeroScheme_euler_eq_sectionOrder
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) (hs : s ≠ 0) (d : ℕ) :
    eulerCharacteristic
      (CurveZeroEuler.algebraStructureMap (A ⧸ Ideal.span {localCoefficient e s})) d
      (structureSheaf (zeroScheme e s)) = ((sectionOrder e s).toNat : ℤ) :=
  CurveZeroEuler.principal_zero_euler_eq_order ((localCoefficient_eq_zero_iff e s).not.mpr hs) d

end PiExponent.LocalSectionOrder

end

end OAI
