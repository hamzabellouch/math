import OAI.GroupTheory.PolycyclicRecognition.Algebra.ControlledPrismIdentity

namespace OAI

/-! # The cochain equation for the controlled prism -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {G H R : Type} [Group G] [Group H] [CommRing R] {n : ℕ}

theorem controlledPrism_equation_succ (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (c : controlledCochains R H (n + 1)) :
    controlledCochainPullback e (n + 1) c =
      controlledCoboundary (controlledPrism e e' hc c) +
        controlledPrism e e' hc (controlledCoboundary c) +
          controlledCochainPullback e' (n + 1) c := by
  have h := (tupleChainPrism (R := R) e.toFun e'.toFun).comm (n + 1)
  rw [dNext_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
    prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at h
  have hh := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp] at hh
  apply controlledLinearExtension_injective
  change controlledLinearExtensionMap _ = controlledLinearExtensionMap _
  simp only [map_add]
  change controlledLinearExtension (controlledCochainPullback e (n + 1) c) =
    controlledLinearExtension (controlledCoboundary (controlledPrism e e' hc c)) +
      controlledLinearExtension (controlledPrism e e' hc (controlledCoboundary c)) +
        controlledLinearExtension (controlledCochainPullback e' (n + 1) c)
  rw [controlledLinearExtension_pullback, controlledLinearExtension_coboundary,
    controlledLinearExtension_prism, controlledLinearExtension_prism,
    controlledLinearExtension_coboundary, controlledLinearExtension_pullback,
    ← tupleChainComplex_boundary_linear, ← tupleChainComplex_boundary_linear, hh]
  erw [LinearMap.comp_add, LinearMap.comp_add]
  rfl

theorem controlledPrism_equation_zero (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (c : controlledCochains R H 0) :
    controlledCochainPullback e 0 c =
      controlledPrism e e' hc (controlledCoboundary c) + controlledCochainPullback e' 0 c := by
  have h := (tupleChainPrism (R := R) e.toFun e'.toFun).comm 0
  rw [dNext_eq_zero _ _ (by simp),
    prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel 1 0), zero_add] at h
  have hh := congrArg ModuleCat.Hom.hom h
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp] at hh
  apply controlledLinearExtension_injective
  change controlledLinearExtensionMap _ = controlledLinearExtensionMap _
  simp only [map_add]
  change controlledLinearExtension (controlledCochainPullback e 0 c) =
      controlledLinearExtension (controlledPrism e e' hc (controlledCoboundary c)) +
        controlledLinearExtension (controlledCochainPullback e' 0 c)
  rw [controlledLinearExtension_pullback, controlledLinearExtension_prism,
    controlledLinearExtension_coboundary, controlledLinearExtension_pullback,
    ← tupleChainComplex_boundary_linear, hh]
  erw [LinearMap.comp_add]
  rfl

end PolycyclicRecognition

end

end OAI
