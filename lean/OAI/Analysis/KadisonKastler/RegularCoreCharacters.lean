import OAI.Analysis.KadisonKastler.RegularCoreRepresentation
import Mathlib.Analysis.Complex.Circle

namespace OAI

/-! # Character multiplication in the regular core representation

The operators `Q_a` are actual multiplication unitaries on `L²(ℝ,H)`.
Their covariance with translations and their commutation with `π(B(H))`
are proved on representatives. These are the generator identities in
the dual-character argument of Section 8.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def regularCharacterScalar (a t : ℝ) : ℂ := Circle.exp (a * t)

theorem regularCharacterScalar_add_left (a b t : ℝ) :
    regularCharacterScalar (a + b) t =
      regularCharacterScalar a t * regularCharacterScalar b t := by
  simp only [regularCharacterScalar, add_mul, Circle.exp_add, Circle.coe_mul]

theorem regularCharacterScalar_add_right (a t s : ℝ) :
    regularCharacterScalar a (t + s) =
      regularCharacterScalar a t * regularCharacterScalar a s := by
  simp only [regularCharacterScalar, mul_add, Circle.exp_add, Circle.coe_mul]

theorem regularCharacterScalar_continuous (a : ℝ) : Continuous (regularCharacterScalar a) :=
  (continuous_subtype_val.comp Circle.exp.continuous).comp (continuous_const.mul continuous_id)

def regularCharacterFiber (a t : ℝ) : unitary (H →L[ℂ] H) :=
  ⟨regularCharacterScalar a t • (1 : H →L[ℂ] H), by
    have hz : star (regularCharacterScalar a t) * regularCharacterScalar a t = (1 : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']
      simp only [regularCharacterScalar, Circle.norm_coe, one_pow, Complex.ofReal_one]
    have hz' : regularCharacterScalar a t * star (regularCharacterScalar a t) = (1 : ℂ) := by
      rw [mul_comm, hz]
    constructor
    · simp only [star_smul, star_one, smul_mul_assoc, mul_smul_comm,
        one_mul, smul_smul, hz', one_smul]
    · simp only [star_smul, star_one, smul_mul_assoc, mul_smul_comm,
        one_mul, smul_smul, hz, one_smul]⟩

theorem regularCharacterFiber_measurable (a : ℝ) (x : H) :
    AEStronglyMeasurable (fun t => (regularCharacterFiber (H := H) a t : H →L[ℂ] H) x) volume := by
  change AEStronglyMeasurable (fun t => regularCharacterScalar a t • x) volume
  exact ((regularCharacterScalar_continuous a).smul continuous_const).aestronglyMeasurable

theorem regularCharacterFiber_star_measurable (a : ℝ) (x : H) :
    AEStronglyMeasurable (fun t => (star (regularCharacterFiber (H := H) a t) : H →L[ℂ] H) x) volume := by
  have he (t : ℝ) : (star (regularCharacterFiber (H := H) a t) : H →L[ℂ] H) x =
      star (regularCharacterScalar a t) • x := by
    simp only [regularCharacterFiber, star_smul, star_one,
      smul_apply, one_apply_eq_self]
  simp only [he]
  exact ((regularCharacterScalar_continuous a).star.smul continuous_const).aestronglyMeasurable

/-- The multiplication unitary `Q_a ξ(t) = exp(i a t) ξ(t)`. -/
def regularCharacterUnitary (a : ℝ) :
    unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
  regularUnitaryField volume (regularCharacterFiber (H := H) a)
    (regularCharacterFiber_measurable a) (regularCharacterFiber_star_measurable a)

theorem regularCharacterUnitary_apply_ae (a : ℝ) (f : RegularCoreHilbert H) :
    (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =ᵐ[volume]
      fun t : ℝ => regularCharacterScalar a t • f t := by
  exact regularUnitaryField_apply_ae volume _ _ _ f

theorem regularCharacterUnitary_zero :
    regularCharacterUnitary (H := H) 0 = 1 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae 0 f] with t ht
  change (regularCharacterUnitary (H := H) 0 :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f t = f t
  simpa only [regularCharacterScalar, zero_mul, Circle.exp_zero, Circle.coe_one,
    one_smul, one_apply_eq_self] using ht

theorem regularCharacterUnitary_add (a b : ℝ) :
    regularCharacterUnitary (H := H) (a + b) =
      regularCharacterUnitary (H := H) a * regularCharacterUnitary (H := H) b := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae (a + b) f,
    regularCharacterUnitary_apply_ae a
      ((regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae b f] with t hab ha hb
  change (regularCharacterUnitary (H := H) (a + b) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f t =
    (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hab, ha, hb, regularCharacterScalar_add_left, mul_smul]

/-- The actual unitary representation defining the dual-character action. -/
def regularCharacterRepresentation : Multiplicative ℝ →* unitary
    (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) where
  toFun a := regularCharacterUnitary (H := H) a.toAdd
  map_one' := regularCharacterUnitary_zero
  map_mul' a b := regularCharacterUnitary_add a.toAdd b.toAdd

theorem regularCharacter_commute_embedding
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (a : ℝ) (T : H →L[ℂ] H) :
    Commute (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCoreEmbedding U hU T) := by
  change (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * regularCoreEmbedding U hU T =
    regularCoreEmbedding U hU T * (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae a (regularCoreEmbedding U hU T f),
    regularCoreEmbedding_apply_ae U hU T f,
    regularCoreEmbedding_apply_ae U hU T
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae a f] with t hQ hπ hπQ hq
  change (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCoreEmbedding U hU T f) t =
    regularCoreEmbedding U hU T
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hQ, hπ, hπQ, hq]
  simp only [map_smul]

/-- The dual characters fix every embedded operator. -/
theorem regularCharacter_fixes_embedding
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (a : ℝ) (T : H →L[ℂ] H) :
    unitaryConj (regularCharacterUnitary (H := H) a) (regularCoreEmbedding U hU T) =
      regularCoreEmbedding U hU T :=
  (commute_unitary_iff_star_right_conjugate (regularCharacterUnitary (H := H) a).property).mp
    (regularCharacter_commute_embedding U hU a T)

/-- Translation/character covariance, proved directly on `L²` classes. -/
theorem regularTranslation_character_covariance (a : ℝ) (s : Multiplicative ℝ) :
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularCharacterUnitary (H := H) a =
      regularCharacterScalar a s.toAdd •
        ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
          regularRightTranslation (H := H) s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularRightTranslation_apply_ae s
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularCharacterUnitary_apply_ae a f),
    regularCharacterUnitary_apply_ae a
      ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f,
    Lp.coeFn_smul (regularCharacterScalar a s.toAdd)
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f))]
    with t hρQ hQshift hQρ hρ hsmul
  simp only [Function.comp_def] at hQshift
  change (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t =
    (regularCharacterScalar a s.toAdd •
      ((regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        ((regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f))) t
  rw [hρQ, hQshift, hsmul]
  simp only [Pi.smul_apply]
  rw [hQρ, hρ, regularCharacterScalar_add_right, smul_smul, mul_comm]

end

end KadisonKastler

end OAI
