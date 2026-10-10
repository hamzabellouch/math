import OAI.Algebra.AuslanderReiten.Modules.TInducedHom
import OAI.Algebra.AuslanderReiten.Ext.ExtendShortExact
import OAI.Algebra.AuslanderReiten.Homology.DerivedHomVanishing
import OAI.Algebra.AuslanderReiten.Homology.TriangleRecurrence

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q
local notation "T" => ArExplicit.T k q

def tExtendedSequence : ShortComplex (CochainComplex (ModuleCat T) ℤ) :=
  (TrivialInduction.sequence (k := k) (complex q)).map
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat T))

theorem tExtendedSequence_shortExact : (tExtendedSequence q).ShortExact :=
  extend_shortExact _ _ (TrivialInduction.sequence_shortExact (complex q))

variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

def tSimpleDerived : DerivedCategory (ModuleCat T) :=
  (DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))

def tInducedDerived : DerivedCategory (ModuleCat T) :=
  DerivedCategory.Q.obj (tInducedCochain q)

def tTriangleA (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    (tSimpleDerived q)⟦(2 : ℤ)⟧ ⟶ tInducedDerived q :=
  (tDualDerivedIso q hq hq1 h).inv ≫ DerivedCategory.Q.map (tExtendedSequence q).f

def tTriangleB (h : NoPositivePowerOne q) : tInducedDerived q ⟶ tSimpleDerived q :=
  DerivedCategory.Q.map (tExtendedSequence q).g ≫ (tQuotientDerivedIso q h).hom

def tTriangleD (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    tSimpleDerived q ⟶ ((tSimpleDerived q)⟦(2 : ℤ)⟧)⟦(1 : ℤ)⟧ :=
  (tQuotientDerivedIso q h).inv ≫
    DerivedCategory.triangleOfSESδ (tExtendedSequence_shortExact q) ≫
      (tDualDerivedIso q hq hq1 h).hom⟦(1 : ℤ)⟧'

def tInductionTriangle (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :=
  Pretriangulated.Triangle.mk (tTriangleA q hq hq1 h) (tTriangleB q h) (tTriangleD q hq hq1 h)

def tInductionTriangleIso (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    DerivedCategory.triangleOfSES (tExtendedSequence_shortExact q) ≅ tInductionTriangle q hq hq1 h :=
  Pretriangulated.Triangle.isoMk _ _ (tDualDerivedIso q hq hq1 h) (Iso.refl _)
    (tQuotientDerivedIso q h)
    (by exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm)
    (by exact (Category.id_comp _).symm)
    (by exact (Iso.hom_inv_id_assoc _ _).symm)

theorem tInductionTriangle_distinguished (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) :
    tInductionTriangle q hq hq1 h ∈ distTriang (DerivedCategory (ModuleCat T)) :=
  Pretriangulated.isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished (tExtendedSequence_shortExact q))
    _ (tInductionTriangleIso q hq hq1 h).symm

theorem tInducedDerived_hom_zero (hq1 : 1 + q ≠ 0) (n : ℤ) (hn : n ≠ 0)
    (f : tInducedDerived q ⟶ (tSimpleDerived q)⟦n⟧) : f = 0 :=
  derivedHom_zero_of_cochain_zero (tInducedCochain q)
    ((CochainComplex.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))) n
    (tInduced_fullCochain_zero q hq1 n hn) f

end ArExplicit.Resolution

end

end OAI
