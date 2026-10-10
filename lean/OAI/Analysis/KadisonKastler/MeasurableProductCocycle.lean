import OAI.Analysis.KadisonKastler.ProductBoundaryCocycle
import OAI.Analysis.KadisonKastler.OperatorMeanEquivariance
import OAI.Analysis.KadisonKastler.HilbertCoefficientMeasurable
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # The product cocycle as a measurable operator class

The pointwise two-sided field is measurable and uniformly unitary. Its
class satisfies the separate-action cocycle law even when the original
cocycle and algebra-membership statements hold only almost everywhere.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [Group G] [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace.SeparableSpace H] in
/-- Evaluation of the product field is strongly measurable. -/
theorem productBoundaryValue_aestronglyMeasurable {N : VonNeumannAlgebra H}
    (p : StandardTracialPosition N) (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    (g : G × G) (ξ : H) :
    AEStronglyMeasurable
      (fun x : D × D => (productBoundaryValue p W g x : H →L[ℂ] H) ξ) (μ.prod μ) := by
  have hleft (η : H) : AEStronglyMeasurable
      (fun x : D × D => (W g.1 x.1 : H →L[ℂ] H) η) (μ.prod μ) :=
    (hW g.1 η).comp_fst
  have hright : AEStronglyMeasurable
      (fun x : D × D => conjugationOperator p.conjugation (W g.2 x.2) ξ) (μ.prod μ) := by
    exact p.conjugation.continuous.comp_aestronglyMeasurable
      ((hW g.2 (p.conjugation ξ)).comp_snd)
  exact aestronglyMeasurable_field_apply
    (fun x : D × D => (W g.1 x.1 : H →L[ℂ] H)) hleft
    (fun x => conjugationOperator p.conjugation (W g.2 x.2) ξ) hright

/-- Bundle an everywhere unitary field from measurable evaluations. -/
def measurableUnitaryRepresentative {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (f : X → unitary (H →L[ℂ] H))
    (hf : ∀ ξ, AEStronglyMeasurable (fun x => (f x : H →L[ℂ] H) ξ) ν) :
    unitary (WeakOperatorRepresentative (H := H) ν) := by
  let F : WeakOperatorRepresentative (H := H) ν :=
    WeakOperatorRepresentative.mk (fun x => (f x : H →L[ℂ] H)) 1
      (fun x => norm_unitary_le_one (f x)) hf
      (operator_adjoint_eval_aestronglyMeasurable (fun x => (f x : H →L[ℂ] H)) hf)
  refine ⟨F, ?_, ?_⟩
  · apply WeakOperatorRepresentative.eq_of_eval
    intro x
    change star (f x : H →L[ℂ] H) * (f x : H →L[ℂ] H) = 1
    exact Unitary.star_mul_self_of_mem (f x).property
  · apply WeakOperatorRepresentative.eq_of_eval
    intro x
    change (f x : H →L[ℂ] H) * star (f x : H →L[ℂ] H) = 1
    exact Unitary.mul_star_self_of_mem (f x).property

/-- A uniformly unitary representative of the product field. -/
def productBoundaryRepresentative {N : VonNeumannAlgebra H}
    (p : StandardTracialPosition N) (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    (g : G × G) : unitary (WeakOperatorRepresentative (H := H) (μ.prod μ)) :=
  measurableUnitaryRepresentative (fun x => productBoundaryValue p W g x)
    (productBoundaryValue_aestronglyMeasurable p W hW g)

omit [Group G] [TopologicalSpace G] [DiscreteTopology G] in
@[simp]
theorem productBoundaryRepresentative_eval {N : VonNeumannAlgebra H}
    (p : StandardTracialPosition N) (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    (g : G × G) (x : D × D) :
    WeakOperatorRepresentative.eval
      (productBoundaryRepresentative p W hW g : WeakOperatorRepresentative (H := H) (μ.prod μ)) x =
        (productBoundaryValue p W g x : H →L[ℂ] H) := rfl

/-- The actual bounded family of unitary classes on the product boundary. -/
def productBoundaryClass {N : VonNeumannAlgebra H}
    (p : StandardTracialPosition N) (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ) :
    unitary ((G × G) →ᵇ WeakOperatorField (H := H) (μ.prod μ)) :=
  boundedUnitaryFamily (fun g => Unitary.map (StarMonoidHom.ofClass (operatorFieldQuotient (H := H) (μ.prod μ)))
    (productBoundaryRepresentative p W hW g))

omit [Group G] in
@[simp]
theorem productBoundaryClass_apply {N : VonNeumannAlgebra H}
    (p : StandardTracialPosition N) (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    (g : G × G) :
    (productBoundaryClass p W hW).val g = operatorFieldQuotient (H := H) (μ.prod μ)
      (productBoundaryRepresentative p W hW g : WeakOperatorRepresentative (H := H) (μ.prod μ)) := rfl

/-- The product cocycle law descends from almost-everywhere original laws. -/
theorem productBoundaryClass_cocycle {N : VonNeumannAlgebra H}
    (p : StandardTracialPosition N) (α : NonsingularAction G D μ)
    (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    (hmem : ∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ N)
    (hcoc : ∀ g h, ∀ᵐ x ∂μ,
      (W g x : H →L[ℂ] H) * (W h (α.toPerm g⁻¹ x) : H →L[ℂ] H) =
        (W (g * h) x : H →L[ℂ] H)) (g h : G × G) :
    (productBoundaryClass p W hW).val g *
        α.prod.operatorAction (H := H) g ((productBoundaryClass p W hW).val h) =
      (productBoundaryClass p W hW).val (g * h) := by
  change operatorFieldQuotient (H := H) (μ.prod μ) _ *
      WeakOperatorField.pullback _ _ (operatorFieldQuotient (H := H) (μ.prod μ) _) =
        operatorFieldQuotient (H := H) (μ.prod μ) _
  rw [WeakOperatorField.pullback_quotient, ← map_mul]
  apply (operatorFieldQuotient_eq_iff (μ.prod μ) _ _).mpr
  have hleft := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (hcoc g.1 h.1)
  have hright := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (hcoc g.2 h.2)
  have hmleft := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae ((α.quasi g.1⁻¹).ae (hmem h.1))
  have hmright := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (hmem g.2)
  filter_upwards [hleft, hright, hmleft, hmright] with x hl hr hml hmr
  change (productBoundaryValue p W g x : H →L[ℂ] H) *
      (productBoundaryValue p W h (α.toPerm g.1⁻¹ x.1, α.toPerm g.2⁻¹ x.2) : H →L[ℂ] H) =
    (productBoundaryValue p W (g * h) x : H →L[ℂ] H)
  simp only [productBoundaryValue_coe, Prod.fst_mul, Prod.snd_mul]
  rw [← hl, ← hr, conjugationOperator_mul p.conjugation p.conjugation_involutive]
  have he := p.commute_conjugationOperator (W h.1 (α.toPerm g.1⁻¹ x.1))
    (W g.2 x.2) hml hmr
  calc
    _ = (W g.1 x.1 : H →L[ℂ] H) *
        (conjugationOperator p.conjugation (W g.2 x.2) *
          (W h.1 (α.toPerm g.1⁻¹ x.1) : H →L[ℂ] H)) *
        conjugationOperator p.conjugation (W h.2 (α.toPerm g.2⁻¹ x.2)) := by noncomm_ring
    _ = _ := by rw [← he.eq]; noncomm_ring

/-- The corresponding representation as a family of constant operator classes. -/
def productBoundaryConstantFamily {M : VonNeumannAlgebra H}
    (p : StandardTracialPosition M) (U : G →* unitary (Algebra M)) :
    unitary ((G × G) →ᵇ WeakOperatorField (H := H) (μ.prod μ)) :=
  boundedUnitaryFamily (fun g => Unitary.map (StarMonoidHom.ofClass (operatorFieldConst (H := H) (μ.prod μ)))
    (productBoundaryRepresentation p U g))

omit [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace D]
  [TopologicalSpace.SeparableSpace H] in
/-- The two individual approximation inequalities suffice for the product bound. -/
theorem productBoundaryValue_close_at {M N : VonNeumannAlgebra H}
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (U : G →* unitary (Algebra M)) (W : G → D → unitary (H →L[ℂ] H))
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) - (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ κ)
    (g : G × G) (x : D × D)
    (hl : ‖(W g.1 x.1 : H →L[ℂ] H) - (U g.1 : Algebra M).val‖ ≤ δ)
    (hr : ‖(W g.2 x.2 : H →L[ℂ] H) - (U g.2 : Algebra M).val‖ ≤ δ) :
    ‖(productBoundaryValue pN W g x : H →L[ℂ] H) -
      (productBoundaryRepresentation pM U g : H →L[ℂ] H)‖ ≤ 2 * δ + 2 * κ := by
  exact norm_product_conjugation_sub_le pM.conjugation pN.conjugation
    pN.conjugation_involutive (W g.1 x.1)
    (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.1))
    (W g.2 x.2) (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.2))
    hδ hκ hl hr hJ

/-- Essential original closeness bounds the uniform norm of the product classes. -/
theorem productBoundaryClass_close {M N : VonNeumannAlgebra H}
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (U : G →* unitary (Algebra M)) (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hclose : ∀ g, ∀ᵐ x ∂μ, ‖(W g x : H →L[ℂ] H) - (U g : Algebra M).val‖ ≤ δ)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) - (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ κ) :
    ‖(productBoundaryClass pN W hW).val - (productBoundaryConstantFamily (μ := μ) pM U).val‖ ≤
      2 * δ + 2 * κ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro g
  change ‖operatorFieldQuotient (H := H) (μ.prod μ)
      (productBoundaryRepresentative pN W hW g : WeakOperatorRepresentative (H := H) (μ.prod μ)) -
        operatorFieldConst (H := H) (μ.prod μ) (productBoundaryRepresentation pM U g)‖ ≤ _
  change ‖operatorFieldQuotient (H := H) (μ.prod μ) _ -
    operatorFieldQuotient (H := H) (μ.prod μ)
      (operatorRepresentativeConst (μ.prod μ) (productBoundaryRepresentation pM U g))‖ ≤ _
  rw [← map_sub]
  apply operatorFieldQuotient_norm_le_of_ae (μ.prod μ) _ (by positivity)
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (hclose g.1),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (hclose g.2)] with x hl hr
  exact productBoundaryValue_close_at pM pN U W hδ hκ hJ g x hl hr

end

end KadisonKastler

end OAI
