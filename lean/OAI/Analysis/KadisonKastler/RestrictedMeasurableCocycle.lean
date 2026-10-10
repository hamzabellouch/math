import OAI.Analysis.KadisonKastler.RestrictedOperatorMean
import OAI.Analysis.KadisonKastler.MeasurableOperatorCocycle

namespace OAI

/-! # Measurable cocycle correction with values in a von Neumann algebra -/

namespace KadisonKastler

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

namespace ScalarBoundaryMean

variable {α : NonsingularAction G D μ}

/-- The scalar boundary mean corrects an M-valued approximate cocycle to
an actual measurable unitary cocycle whose values remain in M. -/
theorem exists_measurable_correction_in (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (M : VonNeumannAlgebra H)
    (V : unitary (G →ᵇ operatorFieldAlgebra (μ := μ) M))
    (hV : unitaryCocycleDefect (α.restrictedOperatorAction M) V ≤ 1 / 64) :
    ∃ U : G → D → unitary (H →L[ℂ] H),
      (∀ g ξ, AEStronglyMeasurable (fun x => (U g x : H →L[ℂ] H) ξ) μ) ∧
      (∀ g, ∀ᵐ x ∂μ, (U g x : H →L[ℂ] H) ∈ M) ∧
      (∀ g h, ∀ᵐ x ∂μ,
        (U g x : H →L[ℂ] H) * (U h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
          (U (g * h) x : H →L[ℂ] H)) ∧
      (∀ g, ∀ᵐ x ∂μ,
        ‖(U g x : H →L[ℂ] H) - WeakOperatorRepresentative.eval
          (WeakOperatorField.representative (V.val g : WeakOperatorField (H := H) μ)) x‖ ≤
            2 * unitaryCocycleDefect (α.restrictedOperatorAction M) V) := by
  obtain ⟨W, hW, hd⟩ := m.exists_restricted_operator_cocycle hTom M V hV
  let inc := operatorFieldFamilyInclusion (G := G) (μ := μ) M
  let V' : unitary (G →ᵇ WeakOperatorField (H := H) μ) :=
    Unitary.map (StarMonoidHom.ofClass inc) V
  let W' : unitary (G →ᵇ WeakOperatorField (H := H) μ) :=
    Unitary.map (StarMonoidHom.ofClass inc) W
  have hW' (g h : G) :
      W'.val g * α.operatorAction (H := H) g (W'.val h) = W'.val (g * h) := by
    exact congrArg (fun q : operatorFieldAlgebra (μ := μ) M =>
      (q : WeakOperatorField (H := H) μ)) (hW g h)
  have hd' : dist V' W' ≤ 2 * unitaryCocycleDefect (α.restrictedOperatorAction M) V := by
    rw [Subtype.dist_eq, dist_eq_norm]
    change ‖inc V.val - inc W.val‖ ≤ _
    have hd₀ : ‖V.val - W.val‖ ≤ 2 * unitaryCocycleDefect (α.restrictedOperatorAction M) V := by
      simpa only [Subtype.dist_eq, dist_eq_norm] using hd
    have hi : inc (V.val - W.val) = inc V.val - inc W.val := by
      ext g
      rfl
    calc
      _ = ‖inc (V.val - W.val)‖ := congrArg norm hi.symm
      _ ≤ ‖V.val - W.val‖ :=
        norm_operatorFieldFamilyInclusion_le (G := G) (μ := μ) M (V.val - W.val)
      _ ≤ _ := hd₀
  obtain ⟨U, hm, hc, hclose, hrep⟩ :=
    exists_measurable_operator_cocycle_with_lift α V' W' hW' hd'
  refine ⟨U, hm, ?_, hc, hclose⟩
  intro g
  have hv := hasOperatorValues_of_mem M
    (W.val g : WeakOperatorField (H := H) μ) (W.val g).property
  filter_upwards [hrep g, hv] with x hx hmem
  rwa [hx]

end ScalarBoundaryMean

end

end KadisonKastler

end OAI
