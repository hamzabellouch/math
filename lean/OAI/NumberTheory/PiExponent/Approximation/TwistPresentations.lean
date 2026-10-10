import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation
import OAI.NumberTheory.PiExponent.LocalAlgebra.SerreDimensionShift

namespace OAI

namespace PiExponent.GeometrySupport.TwistPresentations
noncomputable section
universe w
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

private abbrev schemeUnit (X : Scheme.{0}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

variable {X : Scheme.{0}}

def twistShiftIso (L : LineBundle X) (M : X.Modules) (n0 n : ℕ) :
    (moduleTwistFunctor L n).obj ((moduleTwistFunctor L n0).obj M) ≅
      (moduleTwistFunctor L (n0+n)).obj M :=
  eqToIso (by rw [moduleTwistFunctor_add]; rfl)

def twistFreeIsoBiproduct [HasFiniteBiproducts X.Modules]
    (L : LineBundle X) (n : ℕ) (I : Type) [Fintype I] :
    (moduleTwistFunctor L n).obj (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      ⨁ (fun _ : I => modulePow X L.sheaf n) :=
  (moduleTwistFunctor L n).mapIso
      (biproduct.isoCoproduct (fun _ : I => structureSheaf X)).symm ≪≫
    (moduleTwistFunctor L n).mapBiproduct (fun _ : I => structureSheaf X) ≪≫
    biproduct.mapIso (fun _ : I => moduleTwistUnitIso L n)

variable (L : LineBundle X) {M : X.Modules} {n0 : ℕ}
    (s : ((moduleTwistFunctor L n0).obj M).GeneratingSections)

abbrev presentationKernel : X.Modules := kernel (C := X.Modules) s.π

abbrev presentationMiddle (n : ℕ) : X.Modules :=
  (moduleTwistFunctor L n).obj (SheafOfModules.free s.I)

def presentationLeft (n : ℕ) :
    (moduleTwistFunctor L n).obj (presentationKernel L s) ⟶ presentationMiddle L s n :=
  (moduleTwistFunctor L n).map (kernel.ι (C := X.Modules) s.π)

def presentationRight (n : ℕ) :
    presentationMiddle L s n ⟶ (moduleTwistFunctor L (n0+n)).obj M :=
  (moduleTwistFunctor L n).map s.π ≫ (twistShiftIso L M n0 n).hom

theorem presentation_comp_zero (n : ℕ) :
    presentationLeft L s n ≫ presentationRight L s n = 0 := by
  unfold presentationLeft presentationRight
  erw [← Category.assoc, ← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]

theorem presentation_shortExact (n : ℕ) :
    (ShortComplex.mk (presentationLeft L s n) (presentationRight L s n)
      (presentation_comp_zero L s n)).ShortExact := by
  have : Epi s.π := s.epi
  have hbase : (ShortComplex.kernelSequence (C := X.Modules) s.π).ShortExact := {
    exact := ShortComplex.kernelSequence_exact s.π
    mono_f := equalizer.ι_mono (C := X.Modules) (f := s.π)
    epi_g := s.epi }
  have : Functor.PreservesZeroMorphisms (C := X.Modules) (D := X.Modules)
      (moduleTwistFunctor L n) := inferInstance
  let T := (ShortComplex.kernelSequence (C := X.Modules) s.π).map (moduleTwistFunctor L n)
  let e : T ≅ ShortComplex.mk (presentationLeft L s n) (presentationRight L s n)
      (presentation_comp_zero L s n) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (twistShiftIso L M n0 n)
      (by
        simp only [presentationLeft]
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
      (by
        simp only [presentationRight]
        exact Category.id_comp _)
  exact ShortComplex.shortExact_of_iso e (moduleTwistFunctor_shortExact L n _ hbase)

theorem presentationKernel_isFinitePresentation [IsLocallyNoetherian X]
    [M.IsFinitePresentation] [s.IsFiniteType] : (presentationKernel L s).IsFinitePresentation := by
  have := PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation L n0 M
  let : ((moduleTwistFunctor L n0).obj M).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((moduleTwistFunctor L n0).obj M)).choose.isQuasicoherent
  exact PiExponent.FiniteGlobalPresentation.kernel_generators_isFinitePresentation _ s

theorem presentationMiddle_ext_zero [HasExt.{w} X.Modules]
    (L : LineBundle X) {M : X.Modules} {n0 : ℕ}
    (s : ((moduleTwistFunctor L n0).obj M).GeneratingSections) [hs : s.IsFiniteType]
    (A : X.Modules)
    (hpow : ∀ n q, 0 < q → ∀ x : Ext.{w} A (modulePow X L.sheaf n) q, x = 0)
    (n q : ℕ) (hq : 0 < q) (x : Ext.{w} A (presentationMiddle L s n) q) : x = 0 := by
  let : Finite s.I := hs.finite
  let : Fintype s.I := Fintype.ofFinite s.I
  let : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  let e := twistFreeIsoBiproduct L n s.I
  let e' := (extFunctorObj A q).mapIso e
  apply (ConcreteCategory.bijective_of_isIso e'.hom).injective
  change e'.hom x = e'.hom 0
  rw [map_zero]
  exact SerreDimensionShift.ext_eq_zero_of_biproduct A
    (biproduct.isBilimit (fun _ : s.I => modulePow X L.sheaf n)) q
    (fun _ => hpow n q hq) (e'.hom x)

def coherentTwistFamily (L : LineBundle X)
    (M : {M : X.Modules // M.IsFinitePresentation}) (n : ℕ) : X.Modules :=
  (moduleTwistFunctor L n).obj M.val

def acyclicPresentationOfGenerators [IsLocallyNoetherian X] [HasExt.{w} X.Modules]
    (L : LineBundle X) (M : {M : X.Modules // M.IsFinitePresentation}) (n0 : ℕ)
    (s : ((moduleTwistFunctor L n0).obj M.val).GeneratingSections) [s.IsFiniteType]
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{w} (C := X.Modules) (schemeUnit X) (modulePow X L.sheaf n) q, x = 0) :
    SerreDimensionShift.AcyclicPresentation.{w} (C := X.Modules) (schemeUnit X)
      (coherentTwistFamily L) M := by
  have : M.val.IsFinitePresentation := M.property
  exact {
    kernel := ⟨presentationKernel L s, presentationKernel_isFinitePresentation L s⟩
    shift := n0
    middle := presentationMiddle L s
    left := presentationLeft L s
    right := presentationRight L s
    comp_zero := presentation_comp_zero L s
    shortExact := presentation_shortExact L s
    acyclic := presentationMiddle_ext_zero L s (schemeUnit X) hpow }

end
end PiExponent.GeometrySupport.TwistPresentations

end OAI
