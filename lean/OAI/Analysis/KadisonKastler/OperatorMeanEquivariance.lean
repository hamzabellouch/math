import OAI.Analysis.KadisonKastler.PublishedFieldTomiyama
import OAI.Analysis.KadisonKastler.WeakFieldPullback

namespace OAI

/-! # The nonsingular action and equivariant operator mean -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

namespace NonsingularAction

variable (α : NonsingularAction G D μ)

/-- Inverse pullback gives the boundary action on actual operator classes. -/
def operatorEquiv (g : G) :
    WeakOperatorField (H := H) μ ≃⋆ₐ[ℂ] WeakOperatorField (H := H) μ where
  toFun := WeakOperatorField.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹)
  invFun := WeakOperatorField.pullback (α.toPerm g) (α.quasi g)
  left_inv q := by
    rw [WeakOperatorField.pullback_comp]
    have h : (α.toPerm g⁻¹ : D → D) ∘ α.toPerm g = id := by
      funext x
      simp only [Function.comp_apply, ← α.mul_apply, inv_mul_cancel, α.one_apply, id_eq]
    simpa only [h] using WeakOperatorField.pullback_id q
  right_inv q := by
    rw [WeakOperatorField.pullback_comp]
    have h : (α.toPerm g : D → D) ∘ α.toPerm g⁻¹ = id := by
      funext x
      simp only [Function.comp_apply, ← α.mul_apply, mul_inv_cancel, α.one_apply, id_eq]
    simpa only [h] using WeakOperatorField.pullback_id q
  map_mul' := (WeakOperatorField.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹)).map_mul
  map_add' := (WeakOperatorField.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹)).map_add
  map_smul' c q := map_smul (WeakOperatorField.pullback (H := H) (α.toPerm g⁻¹) (α.quasi g⁻¹)) c q
  map_star' q := map_star (WeakOperatorField.pullback (H := H) (α.toPerm g⁻¹) (α.quasi g⁻¹)) q

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem operatorEquiv_apply (g : G) (q : WeakOperatorField (H := H) μ) :
    α.operatorEquiv (H := H) g q = WeakOperatorField.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹) q := rfl

/-- The inverse pullbacks form a group action. -/
def operatorAction : G →* (WeakOperatorField (H := H) μ ≃⋆ₐ[ℂ] WeakOperatorField (H := H) μ) where
  toFun := α.operatorEquiv (H := H)
  map_one' := by
    apply StarAlgEquiv.ext
    intro q
    change WeakOperatorField.pullback (α.toPerm (1 : G)⁻¹) (α.quasi (1 : G)⁻¹) q = q
    have h : (α.toPerm (1 : G)⁻¹ : D → D) = id := by funext x; simp
    simpa only [h] using WeakOperatorField.pullback_id q
  map_mul' g h := by
    apply StarAlgEquiv.ext
    intro q
    change WeakOperatorField.pullback (α.toPerm (g * h)⁻¹) _ q =
      WeakOperatorField.pullback (α.toPerm g⁻¹) _ (WeakOperatorField.pullback (α.toPerm h⁻¹) _ q)
    rw [WeakOperatorField.pullback_comp]
    have he : (α.toPerm (g * h)⁻¹ : D → D) = α.toPerm h⁻¹ ∘ α.toPerm g⁻¹ := by
      funext x
      simp only [mul_inv_rev, α.mul_apply, Function.comp_apply]
    simp only [he]

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem operatorAction_coefficient (g : G) (q : WeakOperatorField (H := H) μ) (ξ η : H) :
    WeakOperatorField.coefficient (α.operatorAction (H := H) g q) ξ η =
      scalarInfinityPullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (WeakOperatorField.coefficient q ξ η) :=
  WeakOperatorField.coefficient_pullback _ _ _ _ _

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem operatorAction_constant (g : G) (T : H →L[ℂ] H) :
    α.operatorAction (H := H) g (operatorFieldConst μ T) = operatorFieldConst μ T :=
  WeakOperatorField.pullback_constant _ _ _

end NonsingularAction

namespace WeakOperatorField

omit [TopologicalSpace.SeparableSpace H] in
/-- Scalar coefficients intertwine the two simultaneous translations. -/
theorem coefficientFamily_translate (α : NonsingularAction G D μ) (g : G)
    (F : G →ᵇ WeakOperatorField (H := H) μ) (ξ η : H) :
    coefficientFamily (boundaryTranslate (α.operatorAction (H := H)) g F) ξ η =
      scalarBoundaryTranslate α g (coefficientFamily F ξ η) := by
  apply BoundedContinuousFunction.ext
  intro t
  simp only [coefficientFamily_apply, boundaryTranslate_apply,
    NonsingularAction.operatorAction_coefficient]
  rfl

end WeakOperatorField

namespace ScalarBoundaryMean

variable {α : NonsingularAction G D μ}

/-- Equivariance of the operator mean follows from its scalar coefficient identity. -/
theorem operatorMean_equivariant (m : ScalarBoundaryMean α) (g : G)
    (F : G →ᵇ WeakOperatorField (H := H) μ) :
    m.operatorMean (boundaryTranslate (α.operatorAction (H := H)) g F) =
      α.operatorAction (H := H) g (m.operatorMean F) := by
  apply WeakOperatorField.ext_coeff
  intro ξ η
  rw [operatorMean_apply, m.operatorMeanValue_coefficient,
    NonsingularAction.operatorAction_coefficient, operatorMean_apply,
    m.operatorMeanValue_coefficient, WeakOperatorField.coefficientFamily_translate, m.equivariant]

/-- The constructed equivariant mean now feeds the complete cocycle iteration. -/
theorem exists_operator_cocycle (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (V : unitary (G →ᵇ WeakOperatorField (H := H) μ))
    (hV : unitaryCocycleDefect (α.operatorAction (H := H)) V ≤ 1 / 64) :
    ∃ W : unitary (G →ᵇ WeakOperatorField (H := H) μ),
      (∀ g h, W.val g * α.operatorAction (H := H) g (W.val h) = W.val (g * h)) ∧
      dist V W ≤ 2 * unitaryCocycleDefect (α.operatorAction (H := H)) V :=
  exists_bounded_cocycle_of_equivariant_mean (α.operatorAction (H := H)) (m.operatorBimoduleMean hTom)
    m.operatorMean_equivariant V hV

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
