import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledCochainComplex

namespace OAI

/-! # Coarse pullback as a map of controlled cochain complexes -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G H J R : Type} [Group G] [Group H] [Group J] [CommRing R]

/-- Coarse pullback commutes with the actual homogeneous differential. -/
def controlledCochainMap (e : GroupCoarseEquivalence G H) :
    controlledCochainComplex R H ⟶ controlledCochainComplex R G :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (controlledCochainPullback e n))
    (fun n => by
      rw [controlledCochainComplex_d, controlledCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change controlledCoboundary (controlledCochainPullback e n c) =
        controlledCochainPullback e (n + 1) (controlledCoboundary c)
      exact controlledCoboundary_pullback e c)

@[simp] theorem controlledCochainMap_apply (e : GroupCoarseEquivalence G H)
    (n : ℕ) (c : controlledCochains R H n) (x : Fin (n + 1) → G) :
    ((controlledCochainMap e).f n c : controlledCochains R G n).val x =
      c (e.toFun ∘ x) := rfl

/-- Pullback on complexes reverses composition. -/
theorem controlledCochainMap_trans (e : GroupCoarseEquivalence G H)
    (e' : GroupCoarseEquivalence H J) :
    controlledCochainMap (R := R) (e.trans e') =
      controlledCochainMap e' ≫ controlledCochainMap e := by
  ext n c
  rfl

end PolycyclicRecognition

end

end OAI
