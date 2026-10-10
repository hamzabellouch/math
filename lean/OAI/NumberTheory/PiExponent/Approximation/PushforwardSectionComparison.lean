import OAI.NumberTheory.PiExponent.Approximation.PushforwardOpenSections

namespace OAI

namespace PiExponent.GeometrySupport.PushforwardOpenSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher CechH1Transfer

private abbrev schemeFreeOpen (X : Scheme.{0}) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (β : M ⟶ (Scheme.Modules.pushforward f).obj N)
    {J : Type} (U : J → X.Opens)

theorem intersection_preimage {k : ℕ} (t : Fin k → J) :
    intersection (fun i => f ⁻¹ᵁ U i) t = f ⁻¹ᵁ intersection U t := by
  ext x
  simp [intersection, Opens.coe_iInf]

def tupleSectionMap {k : ℕ} (t : Fin k → J) :
    (schemeFreeOpen X (intersection U t) ⟶ M) →+
      (schemeFreeOpen Y (intersection (fun i => f ⁻¹ᵁ U i) t) ⟶ N) :=
  (restrictEquiv N (le_of_eq (intersection_preimage f U t))
    (le_of_eq (intersection_preimage f U t).symm)).toAddMonoidHom.comp
      (sectionMap f β (intersection U t))

theorem tupleSectionMap_bijective {k : ℕ} (t : Fin k → J)
    (h : Function.Bijective (β.app (intersection U t))) :
    Function.Bijective (tupleSectionMap f β U t) :=
  (restrictEquiv N (le_of_eq (intersection_preimage f U t))
    (le_of_eq (intersection_preimage f U t).symm)).bijective.comp
      (sectionMap_bijective f β _ h)

theorem tupleSectionMap_injective {k : ℕ} (t : Fin k → J)
    (h : Function.Injective (β.app (intersection U t))) :
    Function.Injective (tupleSectionMap f β U t) :=
  (restrictEquiv N (le_of_eq (intersection_preimage f U t))
    (le_of_eq (intersection_preimage f U t).symm)).injective.comp
      (sectionMap_injective f β _ h)

theorem tupleSectionMap_face {k : ℕ} (t : Fin (k+2) → J) (j : Fin (k+2))
    (b : schemeFreeOpen X (intersection U (t ∘ j.succAbove)) ⟶ M) :
    tupleSectionMap f β U t (restrictHom X.ringCatSheaf (faceLE U t j) b) =
      restrictHom Y.ringCatSheaf (faceLE (fun i => f ⁻¹ᵁ U i) t j)
        (tupleSectionMap f β U (t ∘ j.succAbove) b) := by
  change restrictHom Y.ringCatSheaf _
      (sectionMap f β _ (restrictHom X.ringCatSheaf _ b)) =
    restrictHom Y.ringCatSheaf _
      (restrictHom Y.ringCatSheaf _ (sectionMap f β _ b))
  erw [sectionMap_restrict, restrictHom_restrictHom, restrictHom_restrictHom]

def comparison
    (hvertex : ∀ t : Fin 1 → J, Function.Bijective (β.app (intersection U t)))
    (hpair : ∀ t : Fin 2 → J, Function.Injective (β.app (intersection U t))) :
    SectionComparison U (fun i => f ⁻¹ᵁ U i) M N where
  vertex t := AddEquiv.ofBijective (tupleSectionMap f β U t)
    (tupleSectionMap_bijective f β U t (hvertex t))
  pair t := tupleSectionMap f β U t
  triple t := tupleSectionMap f β U t
  pair_injective t := tupleSectionMap_injective f β U t (hpair t)
  pair_restrict t j b := tupleSectionMap_face f β U t j b
  triple_restrict t j b := tupleSectionMap_face f β U t j b

end
end PiExponent.GeometrySupport.PushforwardOpenSections

end OAI
