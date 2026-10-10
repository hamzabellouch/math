import OAI.Analysis.ModularTheory.DualAction

namespace OAI

/-! The dual action as actual star algebra automorphisms of the concrete
modular core, including its group law. -/

noncomputable section
open MeasureTheory

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ) [Measure.IsAddRightInvariant μ]
  (S : BoundedRecovery.StandardModularData H)

omit [Measure.IsAddRightInvariant μ] in
lemma modularDualConjugation_apply (r : ℝ) (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (f : Lp H 2 μ) :
    modularDualConjugation μ r T f = modularDual μ r (T (modularDual μ (-r) f)) := rfl

omit [Measure.IsAddRightInvariant μ] in
lemma modularDualConjugation_comp (r s : ℝ) (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    modularDualConjugation μ r (modularDualConjugation μ s T) =
      modularDualConjugation μ (r + s) T := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [modularDualConjugation_apply]
  rw [modularDual_comp, modularDual_comp]
  rw [show -s + -r = -(r + s) by ring]

omit [Measure.IsAddRightInvariant μ] in
@[simp] lemma modularDualConjugation_zero (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    modularDualConjugation μ 0 T = T := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [modularDualConjugation_apply, neg_zero, modularDual_zero]

def modularCoreDualHom (r : ℝ) : (modularCrossedProduct μ S).toStarSubalgebra →⋆ₐ[ℂ]
    (modularCrossedProduct μ S).toStarSubalgebra :=
  ((modularDualConjugation (H := H) μ r).toStarAlgHom.comp
    (modularCrossedProduct μ S).toStarSubalgebra.subtype).codRestrict
      (modularCrossedProduct μ S).toStarSubalgebra
      (fun a => modularDualConjugation_mem μ S r a.property)

lemma modularCoreDualHom_comp (r s : ℝ)
    (a : (modularCrossedProduct μ S).toStarSubalgebra) :
    modularCoreDualHom μ S r (modularCoreDualHom μ S s a) =
      modularCoreDualHom μ S (r + s) a := by
  apply Subtype.ext
  exact modularDualConjugation_comp μ r s a.val

@[simp] lemma modularCoreDualHom_zero
    (a : (modularCrossedProduct μ S).toStarSubalgebra) :
    modularCoreDualHom μ S 0 a = a := by
  apply Subtype.ext
  exact modularDualConjugation_zero μ a.val

def modularCoreDualAction (r : ℝ) : (modularCrossedProduct μ S).toStarSubalgebra ≃⋆ₐ[ℂ]
    (modularCrossedProduct μ S).toStarSubalgebra :=
  StarAlgEquiv.ofBijective (modularCoreDualHom μ S r) ⟨by
    intro a b hab
    apply Subtype.ext
    apply (modularDualConjugation μ r).injective
    exact congrArg Subtype.val hab, by
    intro a
    refine ⟨modularCoreDualHom μ S (-r) a, ?_⟩
    rw [modularCoreDualHom_comp, add_neg_cancel, modularCoreDualHom_zero]⟩

lemma modularCoreDualAction_comp (r s : ℝ)
    (a : (modularCrossedProduct μ S).toStarSubalgebra) :
    modularCoreDualAction μ S r (modularCoreDualAction μ S s a) =
      modularCoreDualAction μ S (r + s) a :=
  modularCoreDualHom_comp μ S r s a

end WeakPureInfiniteness

end

end OAI
