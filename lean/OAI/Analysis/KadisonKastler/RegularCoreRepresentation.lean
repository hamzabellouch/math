import OAI.Analysis.KadisonKastler.RegularCoreOperators
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

namespace OAI

/-! # The real regular representation and the core embedding

The translation and gauge operators below act on `L²(ℝ,H)` itself. A
strongly continuous unitary group gives the faithful embedding
`π(x)(t) = U(t)* x U(t)`. No crossed-product or fixed-point identification
is assumed in these constructions.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Right translation of actual `L²` classes. -/
def regularTranslateApply (s : ℝ) (f : RegularCoreHilbert H) : RegularCoreHilbert H :=
  Lp.compMeasurePreserving (fun t : ℝ => t + s) (measurePreserving_add_right volume s) f

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularTranslateApply_ae (s : ℝ) (f : RegularCoreHilbert H) :
    regularTranslateApply s f =ᵐ[volume] fun t => f (t + s) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume s)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularTranslateApply_add (s t : ℝ) (f : RegularCoreHilbert H) :
    regularTranslateApply s (regularTranslateApply t f) = regularTranslateApply (s + t) f := by
  apply Lp.ext
  filter_upwards [regularTranslateApply_ae s (regularTranslateApply t f),
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae_eq_comp
      (regularTranslateApply_ae t f), regularTranslateApply_ae (s + t) f]
    with a hs ht hst
  simp only [Function.comp_def] at ht
  rw [hs, ht, hst, add_assoc]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularTranslateApply_zero (f : RegularCoreHilbert H) :
    regularTranslateApply 0 f = f := by
  apply Lp.ext
  filter_upwards [regularTranslateApply_ae 0 f] with t ht
  simpa only [add_zero] using ht

def regularTranslationEquiv (s : ℝ) : RegularCoreHilbert H ≃ₗᵢ[ℂ] RegularCoreHilbert H where
  __ := Lp.compMeasurePreservingₗᵢ ℂ
    (fun t : ℝ => t + s) (measurePreserving_add_right volume s)
  invFun := regularTranslateApply (-s)
  left_inv f := by
    change regularTranslateApply (-s) (regularTranslateApply s f) = f
    rw [regularTranslateApply_add, neg_add_cancel, regularTranslateApply_zero]
  right_inv f := by
    change regularTranslateApply s (regularTranslateApply (-s) f) = f
    rw [regularTranslateApply_add, add_neg_cancel, regularTranslateApply_zero]

/-- The concrete right-translation unitary `ρ_s ξ(t)=ξ(t+s)`. -/
def regularRightTranslation : Multiplicative ℝ →* unitary
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  toFun s := Unitary.linearIsometryEquiv.symm (regularTranslationEquiv s.toAdd)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    change regularTranslateApply (H := H) 0 f = f
    exact regularTranslateApply_zero f
  map_mul' s t := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    change regularTranslateApply (s.toAdd + t.toAdd) f =
      regularTranslateApply s.toAdd (regularTranslateApply t.toAdd f)
    exact (regularTranslateApply_add s.toAdd t.toAdd f).symm

theorem regularRightTranslation_apply_ae (s : Multiplicative ℝ) (f : RegularCoreHilbert H) :
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t => f (t + s.toAdd) :=
  regularTranslateApply_ae s.toAdd f

/-- Constant operators commute with translations. -/
theorem regularConstant_commute_translation (T : H →L[ℂ] H) (s : Multiplicative ℝ) :
    Commute (regularConstantHom volume T)
      (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  change regularConstantHom volume T *
      (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      regularConstantHom volume T
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularConstantHom_apply_ae volume T
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f,
    regularRightTranslation_apply_ae s (regularConstantHom volume T f),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularConstantHom_apply_ae volume T f)] with t hc ht htc hct
  simp only [Function.comp_def] at hct
  change regularConstantHom volume T
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t =
    ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularConstantHom volume T f)) t
  rw [hc, ht, htc, hct]

/-- The constant copy of a unitary as an actual unitary on `L²`. -/
def regularConstantUnitary : unitary (H →L[ℂ] H) →* unitary
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  (Unitary.map (StarMonoidHom.ofClass (regularConstantHom (H := H) volume))).toMonoidHom

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem regularGroup_star_eq (t : ℝ) :
    star (U (Multiplicative.ofAdd t)) = U (Multiplicative.ofAdd (-t)) := by
  change (U (Multiplicative.ofAdd t))⁻¹ = U (Multiplicative.ofAdd t)⁻¹
  exact (map_inv U _).symm

include hU in
theorem regularGroup_star_measurable (x : H) :
    AEStronglyMeasurable
      (fun t : ℝ => (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) x) volume := by
  have he : (fun t : ℝ => (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) x) =
      (fun t : ℝ => (U (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) x) := by
    funext t
    exact congrArg (fun v : unitary (H →L[ℂ] H) => (v : H →L[ℂ] H) x)
      (regularGroup_star_eq U t)
  rw [he]
  exact ((hU x).comp continuous_neg).aestronglyMeasurable

/-- Multiplication by `U_t`, as a unitary on the regular Hilbert space. -/
def regularGauge : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  regularUnitaryField volume (fun t => U (Multiplicative.ofAdd t))
    (fun x => (hU x).aestronglyMeasurable) (regularGroup_star_measurable U hU)

theorem regularGauge_apply_ae (f : RegularCoreHilbert H) :
    (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) (f t) :=
  regularUnitaryField_apply_ae volume _ _ _ f

theorem regularGauge_star_apply_ae (f : RegularCoreHilbert H) :
    (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t : ℝ => (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (f t) := by
  let b := regularUnitaryFieldApply volume (fun t => star (U (Multiplicative.ofAdd t)))
    (regularGroup_star_measurable U hU) f
  have hb : b =ᵐ[volume] fun t : ℝ =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (f t) :=
    regularUnitaryFieldApply_ae volume _ _ f
  have hback : (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) b = f := by
    apply Lp.ext
    filter_upwards [regularGauge_apply_ae U hU b, hb] with t hG hb
    rw [hG, hb]
    exact congrArg (fun T : H →L[ℂ] H => T (f t))
      (Unitary.mul_star_self_of_mem (U (Multiplicative.ofAdd t)).property)
  have heq : (star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f = b := by
    apply (Unitary.linearIsometryEquiv (regularGauge U hU)).injective
    change (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) b
    rw [hback]
    exact congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => T f)
      (Unitary.mul_star_self_of_mem (regularGauge U hU).property)
  rw [heq]
  exact hb

/-- The regular embedding `π(x) = gauge* · constant(x) · gauge`. -/
def regularCoreEmbedding : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  ((Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU))).toStarAlgHom).comp
    (regularConstantHom volume)

theorem regularCoreEmbedding_apply_ae (T : H →L[ℂ] H) (f : RegularCoreHilbert H) :
    regularCoreEmbedding U hU T f =ᵐ[volume] fun t : ℝ =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H)
        (T ((U (Multiplicative.ofAdd t) : H →L[ℂ] H) (f t))) := by
  change (Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU)))
    (regularConstantHom volume T) f =ᵐ[volume] _
  rw [Unitary.conjStarAlgAut_star_apply]
  change (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularConstantHom volume T
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) =ᵐ[volume] _
  filter_upwards [regularGauge_star_apply_ae U hU
      (regularConstantHom volume T
        ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    regularConstantHom_apply_ae volume T
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_apply_ae U hU f] with t hs hc hg
  rw [hs, hc, hg]

theorem regularCoreEmbedding_injective : Function.Injective (regularCoreEmbedding U hU) :=
  (Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU))).injective.comp
    real_regularConstantHom_injective

theorem regularCoreEmbedding_completelyIsometric :
    CompletelyIsometric (regularCoreEmbedding U hU).toAlgHom.toLinearMap :=
  injective_starAlgHom_completelyIsometric _ (regularCoreEmbedding_injective U hU)

/-- The common regular action `U_s ⊗ ρ_s`, without any fixed-point premise. -/
def regularCoreAction : Multiplicative ℝ →* unitary
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  toFun s := regularConstantUnitary (U s) * regularRightTranslation (H := H) s
  map_one' := by simp only [map_one, one_mul]
  map_mul' s t := by
    simp only [map_mul]
    have hc : Commute (regularRightTranslation (H := H) s)
        (regularConstantUnitary (U t)) := by
      change regularRightTranslation (H := H) s * regularConstantUnitary (U t) =
        regularConstantUnitary (U t) * regularRightTranslation (H := H) s
      apply Subtype.ext
      change (regularRightTranslation (H := H) s :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
          regularConstantHom volume (U t : H →L[ℂ] H) =
        regularConstantHom volume (U t : H →L[ℂ] H) *
          (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      exact (regularConstant_commute_translation (U t : H →L[ℂ] H) s).symm.eq
    exact (hc.mul_mul_mul_comm (regularConstantUnitary (U s))
      (regularRightTranslation (H := H) t)).symm

theorem regularCoreAction_apply_ae (s : Multiplicative ℝ) (f : RegularCoreHilbert H) :
    (regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t : ℝ => (U s : H →L[ℂ] H) (f (t + s.toAdd)) := by
  filter_upwards [regularConstantHom_apply_ae volume (U s : H →L[ℂ] H)
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f] with t hc ht
  change regularConstantHom volume (U s : H →L[ℂ] H)
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t = _
  rw [hc, ht]

/-- The gauge turns the common regular action into ordinary translation. -/
theorem regularGauge_intertwines_action (s : Multiplicative ℝ) :
    (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularCoreAction U s =
      (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularGauge U hU := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularGauge_apply_ae U hU
      ((regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCoreAction_apply_ae U s f,
    regularRightTranslation_apply_ae s
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularGauge_apply_ae U hU f)] with t hG hA hR hGs
  simp only [Function.comp_def] at hGs
  change (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t =
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hG, hA, hR, hGs]
  have hmul : U (Multiplicative.ofAdd (t + s.toAdd)) =
      U (Multiplicative.ofAdd t) * U s := map_mul U _ _
  rw [hmul, Submonoid.coe_mul, mul_apply_eq_comp]

theorem regularCoreAction_eq_gauged_translation (s : Multiplicative ℝ) :
    (regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU))
        (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  rw [Unitary.conjStarAlgAut_star_apply]
  have h := congrArg
    (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * T)
    (regularGauge_intertwines_action U hU s)
  simpa only [← mul_assoc, Unitary.coe_star,
    Unitary.star_mul_self_of_mem (regularGauge U hU).property, one_mul] using h

/-- Every embedded operator is fixed by the common regular action. -/
theorem regularCoreEmbedding_fixed (s : Multiplicative ℝ) (T : H →L[ℂ] H) :
    unitaryConj (regularCoreAction U s) (regularCoreEmbedding U hU T) =
      regularCoreEmbedding U hU T := by
  apply (commute_unitary_iff_star_right_conjugate (regularCoreAction U s).property).mp
  have h := (regularConstant_commute_translation T s).symm.map
    (Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU)))
  rw [← regularCoreAction_eq_gauged_translation U hU s] at h
  exact h

end

end KadisonKastler

end OAI
