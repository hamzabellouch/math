import OAI.Analysis.KadisonKastler.PublishedRegularDiagonal
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace OAI

/-! # Finite vector measures for real scalar multipliers

The squared pointwise norm of an L2 vector defines a finite measure.
Character commutation preserves its characteristic function and hence
the measure itself. This yields commutation with every scalar multiplier.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def regularVectorMeasure (f : RegularCoreHilbert H) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (‖f t‖ ^ 2))

instance regularVectorMeasure_finite (f : RegularCoreHilbert H) :
    IsFiniteMeasure (regularVectorMeasure f) := by
  have hi := (Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  exact isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Eventually.of_forall fun t => sq_nonneg ‖f t‖)).mpr hi)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularVectorMeasure_integral (f : RegularCoreHilbert H) (φ : ℝ → ℂ) :
    (∫ t, φ t ∂regularVectorMeasure f) = ∫ t, (‖f t‖ ^ 2 : ℝ) • φ t := by
  have hi := (Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  rw [regularVectorMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]

omit [CompleteSpace H] in
theorem regularScalarMultiplier_apply_ae
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C)
    (f : RegularCoreHilbert H) :
    regularScalarMultiplier φ hφ C hC f =ᵐ[volume] fun t => φ t • f t := by
  unfold regularScalarMultiplier
  filter_upwards [regularFieldOperator_represents volume
    (fun t => φ t • (1 : H →L[ℂ] H)) _ _ _ f] with t ht
  simpa only [smul_apply, one_apply_eq_self] using ht

omit [CompleteSpace H] in
theorem regularVectorMeasure_multiplier
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C)
    (f : RegularCoreHilbert H) :
    inner ℂ f (regularScalarMultiplier φ hφ C hC f) =
      ∫ t, φ t ∂regularVectorMeasure f := by
  rw [L2.inner_def, regularVectorMeasure_integral]
  apply integral_congr_ae
  filter_upwards [regularScalarMultiplier_apply_ae φ hφ C hC f] with t ht
  rw [ht, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.real_smul]
  rw [Complex.ofReal_pow]
  exact mul_comm _ _

theorem regularVectorMeasure_charFun (f : RegularCoreHilbert H) (a : ℝ) :
    charFun (regularVectorMeasure f) a =
      inner ℂ f ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) := by
  rw [charFun_apply_real, regularVectorMeasure_integral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularCharacterUnitary_apply_ae a f] with t ht
  rw [ht, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.real_smul]
  simp only [regularCharacterScalar, Circle.coe_exp, Complex.ofReal_mul, Complex.ofReal_pow]
  exact mul_comm _ _

theorem regularVectorMeasure_unitary_eq
    (U : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hU : ∀ a : ℝ, Commute (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (f : RegularCoreHilbert H) :
    regularVectorMeasure ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      regularVectorMeasure f := by
  apply Measure.ext_of_charFun
  funext a
  rw [regularVectorMeasure_charFun, regularVectorMeasure_charFun]
  have he := congrArg (fun S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => S f)
    (hU a).eq.symm
  change (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
    (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) at he
  rw [he]
  exact Unitary.inner_map_map U _ _

/-- Invariance of all vector measures implies commutation with every
bounded Borel multiplier, by polarization of its quadratic form. -/
theorem unitary_commute_scalarMultiplier_of_characters
    (U : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hU : ∀ a : ℝ, Commute (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    Commute (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularScalarMultiplier φ hφ C hC) := by
  let A := regularScalarMultiplier (H := H) φ hφ C hC
  let B := star (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * A *
    (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  have hquad (f : RegularCoreHilbert H) : inner ℂ f (B f) = inner ℂ f (A f) := by
    change inner ℂ f (star (U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (A ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f))) = _
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
      (regularScalarMultiplier φ hφ C hC
        ((U : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) = _
    rw [regularVectorMeasure_multiplier, regularVectorMeasure_unitary_eq U hU,
      regularVectorMeasure_multiplier]
  have hlin : B.toLinearMap = A.toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro f
    calc
      inner ℂ (B f) f = star (inner ℂ f (B f)) := (inner_conj_symm (B f) f).symm
      _ = star (inner ℂ f (A f)) := congrArg star (hquad f)
      _ = inner ℂ (A f) f := inner_conj_symm (A f) f
  apply (commute_unitary_iff_star_left_conjugate U.property).mpr
  apply ContinuousLinearMap.ext
  intro f
  exact LinearMap.congr_fun hlin f

end

end KadisonKastler

end OAI
