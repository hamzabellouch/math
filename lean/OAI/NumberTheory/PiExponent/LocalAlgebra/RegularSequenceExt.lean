import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt
import OAI.NumberTheory.PiExponent.LocalAlgebra.IteratedKoszulExactness

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {R : Type u} [CommRing R]

def regularSequenceAugmentation (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    (W30.regularSequenceComplex rs).X 0 →ₗ[R] (R ⧸ Ideal.ofList rs) :=
  (W30.regularSequenceComplex_exact rs hreg).choose

theorem regularSequenceAugmentation_spec (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    Function.Surjective (regularSequenceAugmentation rs hreg) ∧
    LinearMap.range ((W30.regularSequenceComplex rs).d 1 0).hom =
      LinearMap.ker (regularSequenceAugmentation rs hreg) ∧
    ∀ n, LinearMap.range ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((W30.regularSequenceComplex rs).d (n + 1) n).hom :=
  (W30.regularSequenceComplex_exact rs hreg).choose_spec

def regularSequenceResolution (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList rs)) :=
  moduleFreeResolutionOfExact (W30.regularSequenceComplex rs)
    (ModuleCat.of R (R ⧸ Ideal.ofList rs))
    (ModuleCat.ofHom (regularSequenceAugmentation rs hreg))
    (by
      apply ModuleCat.hom_ext
      exact LinearMap.range_le_ker_iff.mp (regularSequenceAugmentation_spec rs hreg).2.1.le)
    (regularSequenceAugmentation_spec rs hreg).2.1
    (regularSequenceAugmentation_spec rs hreg).1
    (regularSequenceAugmentation_spec rs hreg).2.2
    (W30.regularSequenceComplex_free rs)

theorem regularSequenceResolution_complex (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    (regularSequenceResolution rs hreg).complex = W30.regularSequenceComplex rs := rfl

def regularSequenceQuotientExtAddEquiv (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (Y : ModuleCat.{u} R) (n : ℕ) :
    Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) Y n ≃+
      CochainComplex.HomComplex.CohomologyClass
        (regularSequenceResolution rs hreg).cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj Y) n :=
  (regularSequenceResolution rs hreg).extAddEquivCohomologyClass

theorem regularSequenceQuotientExt_iff_boundaries (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (Y : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) Y (n + 1)) ↔
      ∀ f : (W30.regularSequenceComplex rs).X (n + 1) ⟶ Y,
        (W30.regularSequenceComplex rs).d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : (W30.regularSequenceComplex rs).X n ⟶ Y,
          (W30.regularSequenceComplex rs).d (n + 1) n ≫ g = f :=
  ext_subsingleton_iff_cocycles_are_boundaries _ Y (regularSequenceResolution rs hreg) n

theorem regularSequenceQuotientExt_above_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (Y : ModuleCat.{u} R)
    (n : ℕ) (hn : rs.length < n) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) Y n) := by
  apply ext_subsingleton_of_isZero_resolution_term _ Y (regularSequenceResolution rs hreg) n
  change IsZero ((W30.regularSequenceComplex rs).X n)
  exact ModuleCat.isZero_iff_subsingleton.mpr (W30.regularSequenceComplex_bounded rs n hn)

theorem regularSequenceQuotientExt_of_dual_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ)
    (hdual : LinearMap.range (((W30.regularSequenceComplex rs).d (n + 1) n).hom.dualMap) =
      LinearMap.ker (((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap)) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) (n + 1)) := by
  apply (regularSequenceQuotientExt_iff_boundaries rs hreg (ModuleCat.of R R) n).mpr
  intro f hf
  have hfker : f.hom ∈
      LinearMap.ker (((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap) := by
    change f.hom.comp ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom = 0
    exact ModuleCat.hom_ext_iff.mp hf
  rw [← hdual] at hfker
  obtain ⟨g, hg⟩ := hfker
  refine ⟨ModuleCat.ofHom g, ?_⟩
  apply ModuleCat.hom_ext
  exact hg

def residueFieldExtAddEquiv [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) Y n ≃+
      CochainComplex.HomComplex.CohomologyClass
        (regularSequenceResolution rs hreg).cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj Y) n := by
  change Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) Y n ≃+ _
  rw [← hmax]
  exact regularSequenceQuotientExtAddEquiv rs hreg Y n

end PiExponentSiegelAux.W31

end

end OAI
