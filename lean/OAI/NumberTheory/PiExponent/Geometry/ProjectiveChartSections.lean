import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex
import OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjectiveChartSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology
private abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} (U : X.Opens) (M : X.Modules)

def framedSectionsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    Γ(M,U) ≃+ Γ(U.toScheme,⊤) :=
  (restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.symm.trans
    { toFun := fun x => e.hom.val.app (op ⊤) x
      invFun := fun x => e.inv.val.app (op ⊤) x
      left_inv := fun x => by
        have h := congrArg (fun f => f.val.app (op ⊤) x) e.hom_inv_id
        exact h
      right_inv := fun x => by
        have h := congrArg (fun f => f.val.app (op ⊤) x) e.inv_hom_id
        exact h
      map_add' := fun x y => map_add _ _ _ }

def framedCoefficientsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    Γ(M,U) ≃+ Γ(X,U) :=
  (framedSectionsEquiv U M e).trans U.topIso.commRingCatIsoToRingEquiv.toAddEquiv

def freeOpenAddEquiv : (schemeFreeOpen X U ⟶ M) ≃+ Γ(M,U) :=
  { freeOpenEquiv X.ringCatSheaf M U with
    map_add' := fun f g => by rfl }

def framedHomCoefficientsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    (schemeFreeOpen X U ⟶ M) ≃+ Γ(X,U) :=
  (freeOpenAddEquiv U M).trans (framedCoefficientsEquiv U M e)

def framedHomRingEquiv {A : Type*} [CommRing A]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (r : Γ(X,U) ≃+* A) :
    (schemeFreeOpen X U ⟶ M) ≃+ A :=
  (framedHomCoefficientsEquiv U M e).trans r.toAddEquiv

open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {R ι : Type} [CommRing R] [Fintype ι] (i : ι) (d : ℤ)

def framedLaurentVertex (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R) :
    (schemeFreeOpen X U ⟶ M) →+ Laurent ι R d :=
  (vertexLaurent i d).toAddMonoidHom.comp (framedHomRingEquiv U M e r).toAddMonoidHom

theorem framedLaurentVertex_regular (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R)
    (s : schemeFreeOpen X U ⟶ M) :
    RegularOn {i} (framedLaurentVertex U M i d e r s) :=
  vertexLaurent_regular i d _

theorem framedLaurentVertex_injective (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R) :
    Function.Injective (framedLaurentVertex U M i d e r) :=
  (vertexLaurent_injective i d).comp (framedHomRingEquiv U M e r).injective

theorem framedLaurentVertex_surjective_regular
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R)
    (p : Laurent ι R d) (hp : RegularOn {i} p) :
    ∃ s : schemeFreeOpen X U ⟶ M, framedLaurentVertex U M i d e r s = p := by
  obtain ⟨b, hb⟩ := vertexLaurent_surjective_regular i d p hp
  refine ⟨(framedHomRingEquiv U M e r).symm b, ?_⟩
  change vertexLaurent i d ((framedHomRingEquiv U M e r)
    ((framedHomRingEquiv U M e r).symm b)) = p
  rw [AddEquiv.apply_symm_apply, hb]

def powerHomRingEquiv {A : Type*} [CommRing A]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (r : Γ(X,U) ≃+* A) (n : ℕ) :
    (schemeFreeOpen X U ⟶ modulePow X M n) ≃+ A :=
  framedHomRingEquiv U (modulePow X M n) (modulePowFrame U e n) r

def framedLaurentOverlap (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s)) :
    (schemeFreeOpen X U ⟶ M) →+ Laurent ι R d :=
  (overlapLaurent i d s).comp (framedHomRingEquiv U M e r).toAddMonoidHom

theorem framedLaurentOverlap_injective (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s)) :
    Function.Injective (framedLaurentOverlap U M i d s e r) :=
  (overlapLaurent_injective i d s).comp (framedHomRingEquiv U M e r).injective

theorem framedLaurentOverlap_regular (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s))
    (b : schemeFreeOpen X U ⟶ M) :
    RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i})))
      (framedLaurentOverlap U M i d s e r b) :=
  overlapLaurent_regular i d s _

theorem framedLaurentOverlap_surjective_regular (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s))
    (p : Laurent ι R d)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i}))) p) :
    ∃ b : schemeFreeOpen X U ⟶ M,
      framedLaurentOverlap U M i d s e r b = p := by
  obtain ⟨a, ha⟩ := overlapLaurent_surjective_regular i d s p hp
  refine ⟨(framedHomRingEquiv U M e r).symm a, ?_⟩
  change overlapLaurent i d s ((framedHomRingEquiv U M e r)
    ((framedHomRingEquiv U M e r).symm a)) = p
  rw [AddEquiv.apply_symm_apply, ha]

end PiExponentSeshadri.ProjectiveChartSections

end

end OAI
