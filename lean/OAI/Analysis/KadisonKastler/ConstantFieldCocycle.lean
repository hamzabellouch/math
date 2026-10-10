import OAI.Analysis.KadisonKastler.RestrictedMeasurableCocycle
import OAI.Analysis.KadisonKastler.UnitaryApproximation

namespace OAI

/-! # Correcting a nearby unitary family into an algebra-valued cocycle -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {N : VonNeumannAlgebra H}

/-- Constant fields with values in the specified von Neumann algebra. -/
def algebraConstantField (N : VonNeumannAlgebra H) :
    Algebra N →⋆ₐ[ℂ] operatorFieldAlgebra (μ := μ) N :=
  ((operatorFieldConst μ).comp N.toStarSubalgebra.subtype).codRestrict
    (operatorFieldAlgebra (μ := μ) N) (fun x => by
      apply (mem_operatorFieldAlgebra_iff N _).mpr
      intro T hT
      change operatorFieldConst μ T * operatorFieldConst μ x =
        operatorFieldConst μ x * operatorFieldConst μ T
      rw [← map_mul, ← map_mul]
      exact congrArg (operatorFieldConst μ)
        (((VonNeumannAlgebra.mem_commutant_iff.mp hT) x x.property).symm))

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem algebraConstantField_coe (x : Algebra N) :
    (algebraConstantField (μ := μ) N x : WeakOperatorField (H := H) μ) =
      operatorFieldConst μ x := rfl

/-- A family of algebra unitaries determines a family of constant unitary fields. -/
def constantAlgebraUnitaryFamily (V : G → unitary (Algebra N)) :
    unitary (G →ᵇ operatorFieldAlgebra (μ := μ) N) :=
  boundedUnitaryFamily (fun g => Unitary.map
    (StarMonoidHom.ofClass (algebraConstantField (μ := μ) N)) (V g))

omit [Group G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
@[simp]
theorem constantAlgebraUnitaryFamily_coe (V : G → unitary (Algebra N)) (g : G) :
    ((constantAlgebraUnitaryFamily (μ := μ) V).val g : WeakOperatorField (H := H) μ) =
      operatorFieldConst μ (V g) := rfl

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
/-- The constant-field cocycle error is bounded by the ordinary group error. -/
theorem constantAlgebraUnitaryFamily_defect_le
    (α : NonsingularAction G D μ) (V : G → unitary (Algebra N))
    {e : ℝ} (he : 0 ≤ e)
    (hV : ∀ g h, ‖(V g : H →L[ℂ] H) * V h - V (g * h)‖ ≤ e) :
    unitaryCocycleDefect (α.restrictedOperatorAction N)
      (constantAlgebraUnitaryFamily (μ := μ) V) ≤ e := by
  apply (BoundedContinuousFunction.norm_le he).mpr
  rintro ⟨g, h⟩
  change ‖((constantAlgebraUnitaryFamily (μ := μ) V).val g *
    α.restrictedOperatorAction N g ((constantAlgebraUnitaryFamily (μ := μ) V).val h) -
      (constantAlgebraUnitaryFamily (μ := μ) V).val (g * h) :
        operatorFieldAlgebra (μ := μ) N)‖ ≤ e
  change ‖operatorFieldConst μ (V g) *
    α.operatorAction (H := H) g (operatorFieldConst μ (V h)) -
      operatorFieldConst μ (V (g * h))‖ ≤ e
  rw [α.operatorAction_constant, ← map_mul, ← map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le (operatorFieldConst (H := H) μ) _).trans (hV g h)

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
/-- The canonical representative of a constant field has the expected value almost everywhere. -/
theorem operatorFieldConst_representative_ae (T : H →L[ℂ] H) :
    ∀ᵐ x ∂μ, WeakOperatorRepresentative.eval
      (WeakOperatorField.representative (operatorFieldConst μ T)) x = T := by
  exact (operatorFieldQuotient_eq_iff μ
    (WeakOperatorField.representative (operatorFieldConst μ T))
    (operatorRepresentativeConst μ T)).mp
      (WeakOperatorField.quotient_representative (operatorFieldConst μ T))

namespace ScalarBoundaryMean

/-- Starting from an actual nearby unitary family, correction supplies a
measurable N-valued cocycle with the explicit total approximation bound. -/
theorem exists_measurable_cocycle_near_representation
    {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (U : G →* unitary (H →L[ℂ] H)) (V : G → unitary (Algebra N))
    {e : ℝ} (he : 0 ≤ e) (hsmall : 3 * e ≤ 1 / 64)
    (hV : ∀ g, ‖(V g : H →L[ℂ] H) - (U g : H →L[ℂ] H)‖ ≤ e) :
    ∃ W : G → D → unitary (H →L[ℂ] H),
      (∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ) ∧
      (∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ N) ∧
      (∀ g h, ∀ᵐ x ∂μ,
        (W g x : H →L[ℂ] H) * W h (α.toPerm g⁻¹ x) = W (g * h) x) ∧
      (∀ g, ∀ᵐ x ∂μ, ‖(W g x : H →L[ℂ] H) - U g‖ ≤ 7 * e) := by
  have hdef := constantAlgebraUnitaryFamily_defect_le α V (by positivity)
    (unitary_family_multiplicative_defect U (fun g => ambientAlgebraUnitary (V g)) hV)
  obtain ⟨W, hm, hN, hc, hn⟩ := m.exists_measurable_correction_in hTom N
    (constantAlgebraUnitaryFamily (μ := μ) V) (hdef.trans hsmall)
  refine ⟨W, hm, hN, hc, ?_⟩
  intro g
  have hrep : ∀ᵐ x ∂μ, WeakOperatorRepresentative.eval
      (WeakOperatorField.representative
        ((constantAlgebraUnitaryFamily (μ := μ) V).val g :
          WeakOperatorField (H := H) μ)) x = (V g : H →L[ℂ] H) := by
    rw [constantAlgebraUnitaryFamily_coe]
    exact operatorFieldConst_representative_ae (μ := μ) (V g : H →L[ℂ] H)
  filter_upwards [hn g, hrep] with x hx hrepr
  rw [hrepr] at hx
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (W g x : H →L[ℂ] H) (V g : H →L[ℂ] H) (U g : H →L[ℂ] H)
  linarith [hV g]

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
