import OAI.Analysis.KadisonKastler.OperatorMeanEquivariance
import OAI.Analysis.KadisonKastler.WeakFieldUnitary

namespace OAI

/-! # Measurable unitary cocycles from the quotient construction -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [DiscreteTopology G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
/-- A quotient-valued cocycle admits measurable, everywhere unitary values.
The cocycle identities and norm bound hold almost everywhere. -/
theorem exists_measurable_operator_cocycle_with_lift
    (α : NonsingularAction G D μ)
    (V W : unitary (G →ᵇ WeakOperatorField (H := H) μ))
    (hW : ∀ g h, W.val g * α.operatorAction (H := H) g (W.val h) = W.val (g * h))
    {r : ℝ} (hclose : dist V W ≤ r) :
    ∃ U : G → D → unitary (H →L[ℂ] H),
      (∀ g ξ, AEStronglyMeasurable (fun x => (U g x : H →L[ℂ] H) ξ) μ) ∧
      (∀ g h, ∀ᵐ x ∂μ,
        (U g x : H →L[ℂ] H) * (U h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
          (U (g * h) x : H →L[ℂ] H)) ∧
      (∀ g, ∀ᵐ x ∂μ,
        ‖(U g x : H →L[ℂ] H) -
          WeakOperatorRepresentative.eval (WeakOperatorField.representative (V.val g)) x‖ ≤ r) ∧
      (∀ g, ∀ᵐ x ∂μ, (U g x : H →L[ℂ] H) =
        WeakOperatorRepresentative.eval (WeakOperatorField.representative (W.val g)) x) := by
  classical
  choose R hR using fun g => WeakOperatorField.exists_unitary_lift (unitaryFamilyEval W g)
  let U : G → D → unitary (H →L[ℂ] H) :=
    fun g => WeakOperatorRepresentative.unitaryEval (R g)
  refine ⟨U, fun g ξ => WeakOperatorRepresentative.unitaryEval_measurable (R g) ξ, ?_, ?_, ?_⟩
  · intro g h
    have hquot : operatorFieldQuotient (H := H) μ
        ((R g : WeakOperatorRepresentative (H := H) μ) *
          WeakOperatorRepresentative.pullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (R h)) =
        operatorFieldQuotient (H := H) μ (R (g * h)) := by
      rw [map_mul, ← WeakOperatorField.pullback_quotient, hR g, hR h, hR (g * h)]
      exact hW g h
    exact (operatorFieldQuotient_eq_iff μ _ _).mp hquot
  · intro g
    let F := (R g : WeakOperatorRepresentative (H := H) μ) -
      WeakOperatorField.representative (V.val g)
    have hnorm : ‖operatorFieldQuotient (H := H) μ F‖ ≤ r := by
      have hg := (V.val - W.val).norm_coe_le_norm g
      have hd : ‖V.val - W.val‖ ≤ r := by
        simpa only [Subtype.dist_eq, dist_eq_norm] using hclose
      calc
        ‖operatorFieldQuotient (H := H) μ F‖ = ‖W.val g - V.val g‖ := by
          rw [map_sub, hR g, WeakOperatorField.quotient_representative]
          rfl
        _ = ‖V.val g - W.val g‖ := norm_sub_rev _ _
        _ ≤ ‖V.val - W.val‖ := hg
        _ ≤ r := hd
    filter_upwards [operatorField_ae_norm_le F] with x hx
    exact hx.trans hnorm

  · intro g
    exact (operatorFieldQuotient_eq_iff μ _ _).mp
      ((hR g).trans (WeakOperatorField.quotient_representative (W.val g)).symm)

omit [DiscreteTopology G] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
/-- A quotient-valued cocycle admits measurable, everywhere unitary values.
The cocycle identities and norm bound hold almost everywhere. -/
theorem exists_measurable_operator_cocycle
    (α : NonsingularAction G D μ)
    (V W : unitary (G →ᵇ WeakOperatorField (H := H) μ))
    (hW : ∀ g h, W.val g * α.operatorAction (H := H) g (W.val h) = W.val (g * h))
    {r : ℝ} (hclose : dist V W ≤ r) :
    ∃ U : G → D → unitary (H →L[ℂ] H),
      (∀ g ξ, AEStronglyMeasurable (fun x => (U g x : H →L[ℂ] H) ξ) μ) ∧
      (∀ g h, ∀ᵐ x ∂μ,
        (U g x : H →L[ℂ] H) * (U h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
          (U (g * h) x : H →L[ℂ] H)) ∧
      (∀ g, ∀ᵐ x ∂μ,
        ‖(U g x : H →L[ℂ] H) -
          WeakOperatorRepresentative.eval (WeakOperatorField.representative (V.val g)) x‖ ≤ r) := by
  obtain ⟨U, hm, hc, hd, _⟩ :=
    exists_measurable_operator_cocycle_with_lift α V W hW hclose
  exact ⟨U, hm, hc, hd⟩

omit [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
/-- Countability makes all cocycle laws and norm bounds simultaneous
on one invariant conull set. -/
theorem measurable_cocycle_invariant_conull [Countable G]
    (α : NonsingularAction G D μ) (U : G → D → unitary (H →L[ℂ] H))
    (L : G → D → H →L[ℂ] H) {r : ℝ}
    (hcoc : ∀ g h, ∀ᵐ x ∂μ,
      (U g x : H →L[ℂ] H) * (U h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
        (U (g * h) x : H →L[ℂ] H))
    (hclose : ∀ g, ∀ᵐ x ∂μ, ‖(U g x : H →L[ℂ] H) - L g x‖ ≤ r) :
    ∃ S : Set D, (∀ᵐ x ∂μ, x ∈ S) ∧
      (∀ g x, x ∈ S → α.toPerm g x ∈ S) ∧
      (∀ x ∈ S, ∀ g h,
        (U g x : H →L[ℂ] H) * (U h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
          (U (g * h) x : H →L[ℂ] H)) ∧
      (∀ x ∈ S, ∀ g, ‖(U g x : H →L[ℂ] H) - L g x‖ ≤ r) := by
  let P : (G × G) ⊕ G → D → Prop := fun i x =>
    match i with
    | Sum.inl gh => (U gh.1 x : H →L[ℂ] H) *
        (U gh.2 (α.toPerm gh.1⁻¹ x) : H →L[ℂ] H) = (U (gh.1 * gh.2) x : H →L[ℂ] H)
    | Sum.inr g => ‖(U g x : H →L[ℂ] H) - L g x‖ ≤ r
  have hP : ∀ i, ∀ᵐ x ∂μ, P i x := by
    intro i
    cases i with
    | inl gh => exact hcoc gh.1 gh.2
    | inr g => exact hclose g
  obtain ⟨S, hS, hinv, hpoint⟩ := α.exists_invariant_conull P hP
  exact ⟨S, hS, hinv, fun x hx g h => hpoint x hx (.inl (g, h)),
    fun x hx g => hpoint x hx (.inr g)⟩

namespace ScalarBoundaryMean

variable {α : NonsingularAction G D μ}

/-- The actual measurable correction theorem from a scalar boundary mean
and the precisely cited Tomiyama bimodularity input. -/
theorem exists_measurable_correction (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (V : unitary (G →ᵇ WeakOperatorField (H := H) μ))
    (hV : unitaryCocycleDefect (α.operatorAction (H := H)) V ≤ 1 / 64) :
    ∃ U : G → D → unitary (H →L[ℂ] H),
      (∀ g ξ, AEStronglyMeasurable (fun x => (U g x : H →L[ℂ] H) ξ) μ) ∧
      (∀ g h, ∀ᵐ x ∂μ,
        (U g x : H →L[ℂ] H) * (U h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
          (U (g * h) x : H →L[ℂ] H)) ∧
      (∀ g, ∀ᵐ x ∂μ,
        ‖(U g x : H →L[ℂ] H) -
          WeakOperatorRepresentative.eval (WeakOperatorField.representative (V.val g)) x‖ ≤
            2 * unitaryCocycleDefect (α.operatorAction (H := H)) V) := by
  obtain ⟨W, hW, hdist⟩ := m.exists_operator_cocycle hTom V hV
  exact exists_measurable_operator_cocycle α V W hW hdist

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
