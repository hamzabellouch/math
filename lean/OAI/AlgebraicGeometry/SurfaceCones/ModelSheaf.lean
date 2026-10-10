import OAI.AlgebraicGeometry.SurfaceCones.CMReflexivity

namespace OAI


/-! The double dual of a module pulled back to the completed cone model. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory
namespace SourceConeMorphism
open KummerSourceModel

abbrev E (M : ModuleCat ExplicitCone.completedRing) : W.Modules :=
  CoherentModelActual.E p M

lemma E_coherent (M : ModuleCat ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] : (E M).IsFinitePresentation := by
  let := ExplicitCone.actualCompletion_noetherian
  exact CoherentModelActual.coherent_E p M

lemma E_torsionFree (M : ModuleCat ExplicitCone.completedRing) (U : W.Opens) :
    @Module.IsTorsionFree Γ(W, U) ((E M).val.obj (Opposite.op U)) _ _
      ((E M).val.obj (Opposite.op U)).isModule :=
  CoherentDual.dual_sections_torsionFree _ U

end SourceConeMorphism

end

end OAI
