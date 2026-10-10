import OAI.Analysis.KadisonKastler.MeasurableOperatorCocycle
import OAI.Analysis.KadisonKastler.BoundaryIntertwiner

namespace OAI

/-! # Measurable representatives of the averaged boundary intertwiner

The operator-field mean and polar normalization construct the intertwiner
in the quotient algebra. The null ideal then gives the exact measurable
operator identity needed by the finite-factor argument.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- A constant operator representation in the actual field quotient. -/
def constantFieldRepresentation (U : G →* unitary (H →L[ℂ] H)) :
    G →* unitary (WeakOperatorField (H := H) μ) :=
  (Unitary.map (StarMonoidHom.ofClass (operatorFieldConst (H := H) μ))).toMonoidHom.comp U

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem constantFieldRepresentation_coe (U : G →* unitary (H →L[ℂ] H)) (g : G) :
    (constantFieldRepresentation (μ := μ) U g : WeakOperatorField (H := H) μ) =
      operatorFieldConst μ (U g) := rfl

namespace ScalarBoundaryMean

/-- The averaged polar intertwiner has measurable everywhere-unitary
values, the same norm bound, and the exact covariance almost everywhere. -/
theorem exists_measurable_boundary_intertwiner
    {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (S : unitary (G →ᵇ WeakOperatorField (H := H) μ))
    (hS : ∀ g h, S.val g * α.operatorAction (H := H) g (S.val h) = S.val (g * h))
    (R : G → unitary (WeakOperatorRepresentative (H := H) μ))
    (hR : ∀ g, operatorFieldQuotient (H := H) μ (R g) = S.val g)
    (U : G →* unitary (H →L[ℂ] H))
    {δ : ℝ} (hδ : δ < 1)
    (hclose : ∀ g, ‖S.val g - operatorFieldConst μ (U g)‖ ≤ δ) :
    ∃ L : D → unitary (H →L[ℂ] H),
      (∀ ξ, AEStronglyMeasurable (fun x => (L x : H →L[ℂ] H) ξ) μ) ∧
      (∀ᵐ x ∂μ, ‖(L x : H →L[ℂ] H) - 1‖ ≤ 2 * δ) ∧
      (∀ g, ∀ᵐ x ∂μ,
        (L x : H →L[ℂ] H) * U g =
          (WeakOperatorRepresentative.unitaryEval (R g) x : H →L[ℂ] H) *
            L (α.toPerm g⁻¹ x)) := by
  let Uc : G →* unitary (WeakOperatorField (H := H) μ) :=
    constantFieldRepresentation (μ := μ) U
  have hUc (g t : G) : α.operatorAction (H := H) g (Uc t : WeakOperatorField (H := H) μ) =
      (Uc t : WeakOperatorField (H := H) μ) := by
    dsimp only [Uc]
    rw [constantFieldRepresentation_coe]
    exact α.operatorAction_constant g (U t : H →L[ℂ] H)
  have hclose' (g : G) : ‖S.val g - (Uc g : WeakOperatorField (H := H) μ)‖ ≤ δ :=
    by
      dsimp only [Uc]
      rw [constantFieldRepresentation_coe]
      exact hclose g
  obtain ⟨L₀, hL₀, hn⟩ := exists_unitary_boundary_intertwiner
    (α.operatorAction (H := H)) (m.operatorBimoduleMean hTom)
    m.operatorMean_equivariant S hS Uc hUc hδ hclose'
  obtain ⟨V, hV⟩ := WeakOperatorField.exists_unitary_lift L₀
  refine ⟨WeakOperatorRepresentative.unitaryEval V,
    WeakOperatorRepresentative.unitaryEval_measurable V, ?_, ?_⟩
  · have hnorm : ‖operatorFieldQuotient (H := H) μ
        ((V : WeakOperatorRepresentative (H := H) μ) - 1)‖ ≤ 2 * δ := by
      rw [_root_.map_sub, _root_.map_one, hV]
      exact hn
    filter_upwards [operatorField_ae_norm_le
      ((V : WeakOperatorRepresentative (H := H) μ) - 1)] with x hx
    exact hx.trans hnorm
  · intro g
    have heq : operatorFieldQuotient (H := H) μ
        ((V : WeakOperatorRepresentative (H := H) μ) *
          operatorRepresentativeConst μ (U g : H →L[ℂ] H)) =
        operatorFieldQuotient (H := H) μ
          ((R g : WeakOperatorRepresentative (H := H) μ) *
            WeakOperatorRepresentative.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹) V) := by
      rw [map_mul, map_mul, hV, hR g, ← WeakOperatorField.pullback_quotient, hV]
      exact hL₀ g
    exact (operatorFieldQuotient_eq_iff μ _ _).mp heq

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
