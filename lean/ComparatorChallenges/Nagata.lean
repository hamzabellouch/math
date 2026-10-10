import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

namespace OAI

/-!
# Nagata's strict inequality for very general complex plane configurations

The exceptional family is chosen before every curve and multiplicity vector.
Closedness means common multihomogeneous zero loci on the product of projective
planes, restricted to the open set of ordered distinct configurations.
-/

noncomputable section

open scoped BigOperators

namespace Nagata.AffineMultiplicity

variable {σ K : Type*} [CommRing K]

def pointIdeal (point : σ → K) : Ideal (MvPolynomial σ K) :=
  RingHom.ker (MvPolynomial.eval point)

def orderAtLeast (point : σ → K) (multiplicity : ℕ)
    (polynomial : MvPolynomial σ K) : Prop :=
  polynomial ∈ pointIdeal point ^ multiplicity

def translateHom (point : σ → K) : MvPolynomial σ K →+* MvPolynomial σ K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun index => MvPolynomial.X index + MvPolynomial.C (point index))

@[simp] theorem translateHom_C (point : σ → K) (coefficient : K) :
    translateHom point (MvPolynomial.C coefficient) = MvPolynomial.C coefficient := by
  simp [translateHom]

@[simp] theorem translateHom_X (point : σ → K) (index : σ) :
    translateHom point (MvPolynomial.X index) = MvPolynomial.X index + MvPolynomial.C (point index) := by
  simp [translateHom]

theorem translateHom_neg_comp (point : σ → K) :
    (translateHom (-point)).comp (translateHom point) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro coefficient; simp
  · intro index; simp [add_assoc]

theorem translateHom_comp_neg (point : σ → K) :
    (translateHom point).comp (translateHom (-point)) = RingHom.id _ := by
  simpa only [neg_neg] using translateHom_neg_comp (-point)

def translateEquiv (point : σ → K) : MvPolynomial σ K ≃+* MvPolynomial σ K :=
  { translateHom point with
    invFun := translateHom (-point)
    left_inv := fun polynomial => RingHom.congr_fun (translateHom_neg_comp point) polynomial
    right_inv := fun polynomial => RingHom.congr_fun (translateHom_comp_neg point) polynomial }

@[simp] theorem translateEquiv_apply (point : σ → K) (polynomial : MvPolynomial σ K) :
    translateEquiv point polynomial = translateHom point polynomial := rfl

theorem translate_ne_zero (point : σ → K) (polynomial : MvPolynomial σ K)
    (nonzero : polynomial ≠ 0) : translateHom point polynomial ≠ 0 := by
  intro translated_zero
  apply nonzero
  apply (translateEquiv point).injective
  simpa only [translateEquiv_apply, map_zero] using translated_zero

theorem translated_support_nonempty (point : σ → K) (polynomial : MvPolynomial σ K)
    (nonzero : polynomial ≠ 0) : (translateHom point polynomial).support.Nonempty :=
  MvPolynomial.support_nonempty.mpr (translate_ne_zero point polynomial nonzero)

/-- The least total degree of a nonzero Taylor coefficient. -/
def ordinaryMultiplicity (point : σ → K) (polynomial : MvPolynomial σ K)
    (nonzero : polynomial ≠ 0) : ℕ :=
  (translateHom point polynomial).support.inf'
    (translated_support_nonempty point polynomial nonzero) Finsupp.degree

end Nagata.AffineMultiplicity

namespace Nagata.ProjectiveGeometry

abbrev PlanePoint := Projectivization ℂ (Fin 3 → ℂ)

abbrev OrderedDistinctPoints (count : ℕ) :=
  {points : Fin count → PlanePoint // Function.Injective points}

structure MultihomogeneousEquation (count : ℕ) where
  polynomial : MvPolynomial (Fin count × Fin 3) ℂ
  multidegree : Fin count → ℕ
  homogeneous : ∀ exponent ∈ polynomial.support, ∀ index,
    (∑ coordinate : Fin 3, exponent (index, coordinate)) = multidegree index

def equationVanishes {count : ℕ} (equation : MultihomogeneousEquation count)
    (points : Fin count → PlanePoint) : Prop :=
  ∀ (vectors : Fin count → Fin 3 → ℂ) (nonzero : ∀ index, vectors index ≠ 0),
    (∀ index, Projectivization.mk ℂ (vectors index) (nonzero index) = points index) →
    MvPolynomial.eval (fun index => vectors index.1 index.2) equation.polynomial = 0

def IsProductZariskiClosed {count : ℕ} (locus : Set (Fin count → PlanePoint)) : Prop :=
  ∃ equations : Set (MultihomogeneousEquation count),
    ∀ points, points ∈ locus ↔ ∀ equation ∈ equations, equationVanishes equation points

def IsConfigurationZariskiClosed {count : ℕ}
    (locus : Set (OrderedDistinctPoints count)) : Prop :=
  ∃ ambient : Set (Fin count → PlanePoint), IsProductZariskiClosed ambient ∧
    ∀ points, points ∈ locus ↔ points.val ∈ ambient

abbrev ChartVariables (chart : Fin 3) := {coordinate : Fin 3 // coordinate ≠ chart}

def dehomogenize (chart : Fin 3) (polynomial : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (ChartVariables chart) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun coordinate => if equal : coordinate = chart then 1
      else MvPolynomial.X ⟨coordinate, equal⟩) polynomial

def chartCoordinates (chart : Fin 3) (point : PlanePoint) : ChartVariables chart → ℂ :=
  fun coordinate => point.rep coordinate.val / point.rep chart

/-- Local multiplicity lower bounds are membership in powers of the point ideal. -/
def multiplicityAtLeast (polynomial : MvPolynomial (Fin 3) ℂ)
    (point : PlanePoint) (multiplicity : ℕ) : Prop :=
  ∀ chart : Fin 3, point.rep chart ≠ 0 →
    AffineMultiplicity.orderAtLeast (chartCoordinates chart point) multiplicity
      (dehomogenize chart polynomial)

theorem chart_exists (point : PlanePoint) : ∃ chart : Fin 3, point.rep chart ≠ 0 := by
  by_contra absent
  apply point.rep_nonzero
  funext chart
  exact Classical.not_not.mp (fun nonzero => absent ⟨chart, nonzero⟩)

end Nagata.ProjectiveGeometry

namespace Nagata.Workers.W30

open UniqueFactorizationMonoid

abbrev TernaryPolynomial := MvPolynomial (Fin 3) ℂ

local instance : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _

def equationMultiplicity (polynomial : TernaryPolynomial) :
    Associates TernaryPolynomial →₀ ℕ :=
  factorization (Associates.mk polynomial)

def associatePrincipalIdeal (associate : Associates TernaryPolynomial) :
    Ideal TernaryPolynomial :=
  (Ideal.associatesEquivIsPrincipal TernaryPolynomial associate).val

def equationIdealCycle (polynomial : TernaryPolynomial) : Ideal TernaryPolynomial →₀ ℕ :=
  (equationMultiplicity polynomial).mapDomain associatePrincipalIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_positive_degree_equation_of_homogeneous_cycle
    (cycle : Ideal TernaryPolynomial →₀ ℕ) (nonzero : cycle ≠ 0)
    (homogeneous : ∀ ideal ∈ cycle.support,
      ideal.IsPrime ∧ ideal ≠ ⊥ ∧ ideal.IsPrincipal ∧
        ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)) :
    ∃ polynomial : TernaryPolynomial,
      polynomial ≠ 0 ∧ polynomial.IsHomogeneous polynomial.totalDegree ∧
        0 < polynomial.totalDegree ∧ equationIdealCycle polynomial = cycle := by
  sorry

end Nagata.Workers.W30

namespace Nagata.W16

abbrev PlanePolynomial := MvPolynomial (Fin 3) ℂ

structure NonzeroHomogeneousForm (degree : ℕ) where
  polynomial : PlanePolynomial
  homogeneous : polynomial.IsHomogeneous degree
  nonzero : polynomial ≠ 0

theorem homogeneous_eval_scale {Variables Coefficient : Type*} [CommSemiring Coefficient]
    {polynomial : MvPolynomial Variables Coefficient} {degree : ℕ}
    (homogeneous : polynomial.IsHomogeneous degree)
    (coordinates : Variables → Coefficient) (scalar : Coefficient) :
    MvPolynomial.eval (fun index => scalar * coordinates index) polynomial =
      scalar ^ degree * MvPolynomial.eval coordinates polynomial := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro exponent supported
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← homogeneous.degree_eq_sum_deg_support supported]
  ac_rfl

open Nagata.ProjectiveGeometry

theorem eval_dehomogenize (chart : Fin 3) (polynomial : PlanePolynomial)
    (coordinates : ChartVariables chart → ℂ) :
    MvPolynomial.eval coordinates (dehomogenize chart polynomial) =
      MvPolynomial.eval
        (fun index => if equal : index = chart then 1 else coordinates ⟨index, equal⟩)
        polynomial := by
  classical
  unfold dehomogenize
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun values : Fin 3 → ℂ => MvPolynomial.eval values polynomial)
  funext index
  by_cases equal : index = chart <;> simp [equal, Function.comp_apply]

theorem eval_dehomogenize_normalized {degree : ℕ} {polynomial : PlanePolynomial}
    (homogeneous : polynomial.IsHomogeneous degree) (chart : Fin 3)
    (coordinates : Fin 3 → ℂ) (chart_nonzero : coordinates chart ≠ 0) :
    MvPolynomial.eval (fun index : ChartVariables chart => coordinates index.val / coordinates chart)
        (dehomogenize chart polynomial) =
      (coordinates chart)⁻¹ ^ degree * MvPolynomial.eval coordinates polynomial := by
  classical
  rw [eval_dehomogenize]
  have normalized :
      (fun index : Fin 3 => if equal : index = chart then (1 : ℂ)
        else coordinates index / coordinates chart) =
        fun index => (coordinates chart)⁻¹ * coordinates index := by
    funext index
    by_cases equal : index = chart
    · subst index
      simp [chart_nonzero]
    · simp [equal, div_eq_mul_inv, mul_comm]
  rw [normalized]
  exact homogeneous_eval_scale homogeneous coordinates (coordinates chart)⁻¹

theorem eval_eq_zero_of_dehomogenize_eq_zero {degree : ℕ} {polynomial : PlanePolynomial}
    (homogeneous : polynomial.IsHomogeneous degree) (chart : Fin 3)
    (chart_zero : dehomogenize chart polynomial = 0)
    (coordinates : Fin 3 → ℂ) (chart_nonzero : coordinates chart ≠ 0) :
    MvPolynomial.eval coordinates polynomial = 0 := by
  have evaluated := congrArg
    (MvPolynomial.eval (fun index : ChartVariables chart => coordinates index.val / coordinates chart))
    chart_zero
  rw [eval_dehomogenize_normalized homogeneous chart coordinates chart_nonzero, map_zero] at evaluated
  exact (mul_eq_zero.mp evaluated).resolve_left (pow_ne_zero degree (inv_ne_zero chart_nonzero))

theorem eq_zero_of_dehomogenize_eq_zero {degree : ℕ} {polynomial : PlanePolynomial}
    (homogeneous : polynomial.IsHomogeneous degree) (chart : Fin 3)
    (chart_zero : dehomogenize chart polynomial = 0) : polynomial = 0 := by
  have multiplied : MvPolynomial.X chart * polynomial = 0 := by
    apply ((MvPolynomial.isHomogeneous_X ℂ chart).mul homogeneous).eq_zero_of_forall_eval_eq_zero
    intro coordinates
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    by_cases chart_nonzero : coordinates chart = 0
    · simp [chart_nonzero]
    · rw [eval_eq_zero_of_dehomogenize_eq_zero homogeneous chart chart_zero coordinates chart_nonzero,
          mul_zero]
  exact (mul_eq_zero.mp multiplied).resolve_left (MvPolynomial.X_ne_zero chart)

theorem dehomogenize_ne_zero {degree : ℕ} {polynomial : PlanePolynomial}
    (homogeneous : polynomial.IsHomogeneous degree) (nonzero : polynomial ≠ 0)
    (chart : Fin 3) : ProjectiveGeometry.dehomogenize chart polynomial ≠ 0 := by
  intro chart_zero
  exact nonzero (eq_zero_of_dehomogenize_eq_zero homogeneous chart chart_zero)

end Nagata.W16

namespace Nagata.Workers.W10

open Nagata.Workers.W30 Nagata.W16

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Nonzero finite cycles of homogeneous prime plane ideals, with natural weights. -/
def EffectivePlaneCurve := {cycle : Ideal TernaryPolynomial →₀ ℕ //
  cycle ≠ 0 ∧ ∀ ideal ∈ cycle.support,
    ideal.IsPrime ∧ ideal ≠ ⊥ ∧ ideal.IsPrincipal ∧
      ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)}

/-- An equation realizing the entire cycle, including repeated components. -/
def curveEquation (curve : EffectivePlaneCurve) : TernaryPolynomial :=
  Classical.choose (exists_positive_degree_equation_of_homogeneous_cycle
    curve.val curve.property.1 curve.property.2)

theorem curveEquation_spec (curve : EffectivePlaneCurve) :
    curveEquation curve ≠ 0 ∧
      (curveEquation curve).IsHomogeneous (curveEquation curve).totalDegree ∧
      0 < (curveEquation curve).totalDegree ∧ equationIdealCycle (curveEquation curve) = curve.val :=
  Classical.choose_spec (exists_positive_degree_equation_of_homogeneous_cycle
    curve.val curve.property.1 curve.property.2)

theorem curveEquation_nonzero (curve : EffectivePlaneCurve) : curveEquation curve ≠ 0 :=
  (curveEquation_spec curve).1

def curveDegree (curve : EffectivePlaneCurve) : ℕ := (curveEquation curve).totalDegree

theorem curveEquation_homogeneous (curve : EffectivePlaneCurve) :
    (curveEquation curve).IsHomogeneous (curveDegree curve) :=
  (curveEquation_spec curve).2.1

def curveForm (curve : EffectivePlaneCurve) : NonzeroHomogeneousForm (curveDegree curve) :=
  ⟨curveEquation curve, curveEquation_homogeneous curve, curveEquation_nonzero curve⟩

end Nagata.Workers.W10

namespace Nagata.ProjectiveGeometry

def formOrdinaryMultiplicity {degree : ℕ} (form : W16.NonzeroHomogeneousForm degree)
    (point : PlanePoint) : ℕ :=
  let chart := Classical.choose (chart_exists point)
  AffineMultiplicity.ordinaryMultiplicity (chartCoordinates chart point)
    (dehomogenize chart form.polynomial)
    (W16.dehomogenize_ne_zero form.homogeneous form.nonzero chart)

end Nagata.ProjectiveGeometry

namespace Nagata.W15

open Nagata.Workers.W10 Nagata.ProjectiveGeometry

def curveOrdinaryMultiplicity (curve : EffectivePlaneCurve) (point : PlanePoint) : ℕ :=
  formOrdinaryMultiplicity (curveForm curve) point

end Nagata.W15

namespace Nagata

open ProjectiveGeometry

def FullNagata : Prop :=
  ∀ count : ℕ, 10 ≤ count →
    ∃ exceptional : ℕ → Set (OrderedDistinctPoints count),
      (∀ index, IsConfigurationZariskiClosed (exceptional index) ∧
        exceptional index ≠ Set.univ) ∧
      (∃ points : OrderedDistinctPoints count, ∀ index, points ∉ exceptional index) ∧
      ∀ points : OrderedDistinctPoints count, (∀ index, points ∉ exceptional index) →
        ∀ degree : ℕ, 1 ≤ degree →
        ∀ polynomial : MvPolynomial (Fin 3) ℂ,
          polynomial ≠ 0 → polynomial.IsHomogeneous degree →
        ∀ multiplicities : Fin count → ℕ,
          (∀ index, multiplicityAtLeast polynomial (points.val index) (multiplicities index)) →
          (∑ index, (multiplicities index : ℝ)) < (degree : ℝ) * Real.sqrt (count : ℝ)

theorem nagata_conjecture :
    ∀ count : ℕ, 10 ≤ count →
      ∃ exceptional : ℕ → Set (OrderedDistinctPoints count),
        (∀ index, IsConfigurationZariskiClosed (exceptional index) ∧
          exceptional index ≠ Set.univ) ∧
        (∃ points : OrderedDistinctPoints count, ∀ index, points ∉ exceptional index) ∧
        ∀ points : OrderedDistinctPoints count, (∀ index, points ∉ exceptional index) →
          ∀ curve : Workers.W10.EffectivePlaneCurve, ∀ multiplicities : Fin count → ℕ,
            (∀ index, multiplicities index ≤ W15.curveOrdinaryMultiplicity curve (points.val index)) →
            (∑ index, (multiplicities index : ℝ)) <
              (Workers.W10.curveDegree curve : ℝ) * Real.sqrt (count : ℝ) := by
  sorry

theorem nagata_conjecture_coordinates : FullNagata := by
  sorry

end Nagata

end

end OAI
