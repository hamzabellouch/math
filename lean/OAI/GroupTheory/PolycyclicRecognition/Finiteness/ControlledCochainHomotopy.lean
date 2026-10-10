import OAI.GroupTheory.PolycyclicRecognition.Algebra.ControlledPrismEquation

namespace OAI

/-! # Close coarse maps give homotopic controlled pullbacks -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {G H R : Type} [Group G] [Group H] [CommRing R]

def controlledPrismHom (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite) (i j : ℕ) :
    (controlledCochainComplex R H).X i ⟶ (controlledCochainComplex R G).X j :=
  if h : j + 1 = i then
    h ▸ (show (controlledCochainComplex R H).X (j + 1) ⟶
      (controlledCochainComplex R G).X j from
        ModuleCat.ofHom (controlledPrism (n := j) e e' hc))
  else 0

@[simp] theorem controlledPrismHom_succ (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite) (n : ℕ) :
    controlledPrismHom (R := R) e e' hc (n + 1) n =
      ModuleCat.ofHom (controlledPrism e e' hc) := by
  unfold controlledPrismHom
  exact dite_eq_left rfl

/-- The controlled-support estimate promotes the simplicial prism to an
actual homotopy between the two cochain maps. -/
def controlledCochainHomotopy (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite) :
    Homotopy (controlledCochainMap (R := R) e) (controlledCochainMap e') where
  hom := controlledPrismHom e e' hc
  zero i j h := by
    exact dite_eq_right h
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq _ (by simp : (ComplexShape.up ℕ).Rel 0 1),
        Homotopy.prevD_zero_cochainComplex, add_zero, controlledPrismHom_succ,
        controlledCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change controlledCochainPullback e 0 c =
        controlledPrism e e' hc (controlledCoboundary c) + controlledCochainPullback e' 0 c
      exact controlledPrism_equation_zero e e' hc c
    | succ n =>
      rw [dNext_eq _ (by simp : (ComplexShape.up ℕ).Rel (n + 1) (n + 2)),
        prevD_eq _ (by simp : (ComplexShape.up ℕ).Rel n (n + 1)),
        controlledPrismHom_succ, controlledPrismHom_succ,
        controlledCochainComplex_d, controlledCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change controlledCochainPullback e (n + 1) c =
        controlledPrism e e' hc (controlledCoboundary c) +
          controlledCoboundary (controlledPrism e e' hc c) +
            controlledCochainPullback e' (n + 1) c
      rw [add_comm (controlledPrism e e' hc (controlledCoboundary c))]
      exact controlledPrism_equation_succ e e' hc c

end PolycyclicRecognition

end

end OAI
