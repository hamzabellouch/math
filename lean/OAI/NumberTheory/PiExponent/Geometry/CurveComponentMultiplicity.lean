import Mathlib
import OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem generic_stalk_isArtinian {X : Scheme.{0}} [IsLocallyNoetherian X]
    (x : X) (hx : closure {x} ∈ irreducibleComponents X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  wlog hX : ∃ R : CommRingCat, X = Spec R
  · obtain ⟨i,x,rfl⟩ := X.affineCover.exists_eq x
    let hNoeth : IsLocallyNoetherian (X.affineCover.X i) :=
      LocallyOfFiniteType.isLocallyNoetherian (X.affineCover.f i)
    have hloc := this x (by
      rw [(X.affineCover.f i).isOpenEmbedding.closure_eq_preimage_closure_image,
        Set.image_singleton]
      exact preimage_mem_irreducibleComponents hx (X.affineCover.f i).isOpenEmbedding
        ⟨X.affineCover.f i x, subset_closure rfl, _, rfl⟩) ⟨_,rfl⟩
    let := hloc
    exact (asIso ((X.affineCover.f i).stalkMap x)).commRingCatIsoToRingEquiv.symm.isArtinianRing
  obtain ⟨R,rfl⟩ := hX
  let : IsNoetherianRing ((Spec R).presheaf.stalk x) := inferInstance
  change PrimeSpectrum R at x
  change closure {x} ∈ irreducibleComponents (PrimeSpectrum R) at hx
  have hp : x.asIdeal ∈ minimalPrimes R := by
    rwa [← PrimeSpectrum.vanishingIdeal_singleton,
      PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
  let : Ring.KrullDimLE 0 ((Spec R).presheaf.stalk x) := by
    exact Ring.KrullDimLE.of_isLocalization x.asIdeal hp ((Spec.structureSheaf R).presheaf.stalk x)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

def componentMultiplicity (X : Scheme.{0}) (C : irreducibleComponents X) : ℕ :=
  (Module.length (X.presheaf.stalk (genericPoints.ofComponent C).val)
    (X.presheaf.stalk (genericPoints.ofComponent C).val)).toNat

theorem componentMultiplicity_pos {X : Scheme.{0}} [IsLocallyNoetherian X]
    (C : irreducibleComponents X) : 0 < componentMultiplicity X C := by
  let x := (genericPoints.ofComponent C).val
  let : IsArtinianRing (X.presheaf.stalk x) :=
    generic_stalk_isArtinian x (genericPoints.ofComponent C).property
  exact ENat.toNat_pos (ne_of_gt Module.length_pos) Module.length_ne_top

def reducedComponent (X : Scheme.{0}) (C : irreducibleComponents X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).subscheme

def reducedComponentι (X : Scheme.{0}) (C : irreducibleComponents X) :
    reducedComponent X C ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).subschemeι

instance reducedComponent_closed (X : Scheme.{0}) (C : irreducibleComponents X) :
    IsClosedImmersion (reducedComponentι X C) := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)
  change IsClosedImmersion I.subschemeι
  infer_instance

instance reducedComponent_integral (X : Scheme.{0}) (C : irreducibleComponents X) :
    IsIntegral (reducedComponent X C) := by
  let Z : Closeds X := ⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hI : (I.support : Set X) = C.val := by
    simp only [I,Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let : IsReduced I.subscheme := NumericalAmpleness.isReduced_vanishingIdeal_subscheme Z
  let : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [hI]
    exact Subtype.irreducibleSpace C.property.1
  change IsIntegral I.subscheme
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def componentCurve {X : Scheme.{0}} (C : irreducibleComponents X)
    (hdim : topologicalKrullDim (C.val : Set X) = 1) :
    NumericalAmpleness.IntegralCurve X := by
  refine {
    scheme := reducedComponent X C
    embedding := reducedComponentι X C
    closedImmersion := inferInstance
    integral := inferInstance
    dimension := ?_ }
  change topologicalKrullDim
    ((Scheme.IdealSheafData.vanishingIdeal
      (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).support : Set X) = 1
  have he : ((Scheme.IdealSheafData.vanishingIdeal
      (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).support : Set X) = C.val := by
    simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [he]
  exact hdim

end
end PiExponent.CurveCycle

end OAI
