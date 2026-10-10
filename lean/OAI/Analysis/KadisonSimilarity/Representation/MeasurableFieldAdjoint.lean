import OAI.Analysis.KadisonSimilarity.Representation.BoundedMeasurableField

namespace OAI

/-! # Adjoint and projection laws for bounded measurable fields

Pointwise adjoint laws pass to the actual L² operators by integrating the
Hilbert inner-product identity. In particular, a measurable field of
orthogonal projections defines an actual orthogonal projection on L².
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A pointwise adjoint field constructs the actual Hilbert-space adjoint. -/
theorem boundedFieldOperator_eq_adjoint_of_ae
    (R S : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (hS : ∀ x : H, AEStronglyMeasurable (fun a => S a x) μ)
    (C D : ℝ) (hRbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (hSbound : ∀ᵐ a ∂μ, ‖S a‖ ≤ D)
    (hadjoint : ∀ᵐ a ∂μ, S a = star (R a)) :
    boundedFieldOperator μ S hS D hSbound =
      (boundedFieldOperator μ R hR C hRbound).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedFieldOperator_action μ S hS D hSbound f,
    boundedFieldOperator_action μ R hR C hRbound g, hadjoint] with a hs hr ha
  rw [hs, hr, ha]
  exact ContinuousLinearMap.adjoint_inner_left (R a) (g a) (f a)

/-- Almost-everywhere selfadjointness of the field yields a selfadjoint
bounded L² operator. -/
theorem boundedFieldOperator_isSelfAdjoint
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (hself : ∀ᵐ a ∂μ, IsSelfAdjoint (R a)) :
    IsSelfAdjoint (boundedFieldOperator μ R hR C hbound) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  symm
  apply boundedFieldOperator_eq_adjoint_of_ae μ R R hR hR C C hbound hbound
  exact hself.mono fun _ ha => ha.star_eq.symm

omit [CompleteSpace H] in
/-- Almost-everywhere idempotence passes to the actual operator by its
pointwise action on every L² vector. -/
theorem boundedFieldOperator_isIdempotentElem
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (hidem : ∀ᵐ a ∂μ, IsIdempotentElem (R a)) :
    IsIdempotentElem (boundedFieldOperator μ R hR C hbound) :=
  boundedFieldOperator_left_support μ R hR C hbound
    (boundedFieldOperator μ R hR C hbound) R
    (boundedFieldOperator_action μ R hR C hbound) (hidem.mono fun _ ha => ha.eq)

/-- The reverse field construction preserves orthogonal projections. -/
theorem boundedFieldOperator_isStarProjection
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (hproj : ∀ᵐ a ∂μ, IsStarProjection (R a)) :
    IsStarProjection (boundedFieldOperator μ R hR C hbound) where
  isSelfAdjoint := boundedFieldOperator_isSelfAdjoint μ R hR C hbound
    (hproj.mono fun _ ha => ha.isSelfAdjoint)
  isIdempotentElem := boundedFieldOperator_isIdempotentElem μ R hR C hbound
    (hproj.mono fun _ ha => ha.isIdempotentElem)

/-- The uniform bound needed for a field of orthogonal projections follows
from the projection equations themselves. -/
theorem measurableProjection_norm_bound
    (p : Ω → H →L[ℂ] H) (hp : ∀ᵐ a ∂μ, IsStarProjection (p a)) :
    ∀ᵐ a ∂μ, ‖p a‖ ≤ 1 := hp.mono fun _ ha => IsStarProjection.norm_le _ ha

/-- An actual orthogonal projection from a strongly measurable projection
field; no separate uniform-bound hypothesis is required. -/
def measurableProjectionOperator
    (p : Ω → H →L[ℂ] H)
    (hmeas : ∀ x : H, AEStronglyMeasurable (fun a => p a x) μ)
    (hp : ∀ᵐ a ∂μ, IsStarProjection (p a)) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  boundedFieldOperator μ p hmeas 1 (measurableProjection_norm_bound μ p hp)

theorem measurableProjectionOperator_isStarProjection
    (p : Ω → H →L[ℂ] H)
    (hmeas : ∀ x : H, AEStronglyMeasurable (fun a => p a x) μ)
    (hp : ∀ᵐ a ∂μ, IsStarProjection (p a)) :
    IsStarProjection (measurableProjectionOperator μ p hmeas hp) :=
  boundedFieldOperator_isStarProjection μ p hmeas 1
    (measurableProjection_norm_bound μ p hp) hp

theorem measurableProjectionOperator_action
    (p : Ω → H →L[ℂ] H)
    (hmeas : ∀ x : H, AEStronglyMeasurable (fun a => p a x) μ)
    (hp : ∀ᵐ a ∂μ, IsStarProjection (p a)) (f : Lp H 2 μ) :
    ∀ᵐ a ∂μ, measurableProjectionOperator μ p hmeas hp f a = p a (f a) :=
  boundedFieldOperator_action μ p hmeas 1 (measurableProjection_norm_bound μ p hp) f

theorem measurableProjectionOperator_norm_le
    (p : Ω → H →L[ℂ] H)
    (hmeas : ∀ x : H, AEStronglyMeasurable (fun a => p a x) μ)
    (hp : ∀ᵐ a ∂μ, IsStarProjection (p a)) :
    ‖measurableProjectionOperator μ p hmeas hp‖ ≤ 1 :=
  boundedFieldOperator_norm_le μ p hmeas 1 zero_le_one
    (measurableProjection_norm_bound μ p hp)

end KadisonSimilarity

end

end OAI
