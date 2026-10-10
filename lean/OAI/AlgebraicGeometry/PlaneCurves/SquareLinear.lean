import Lean
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Basic
import OAI.AlgebraicGeometry.PlaneCurves.Forms

namespace OAI

/-!
# Linear algebra, dimensions, and arithmetic of square configurations
-/

section

/-! The square argument can use ambient homogeneous polynomial lifts supplied
by the normal construction. Their entire space already has dimension <k² for
k≥4, so H¹ vanishing and an all-sections restriction theorem are unnecessary. -/
namespace Nagata.Workers.W24

/-- The ambient ternary degree-k form dimension is less than k² for k≥4. -/
theorem ambientDegreeK_dimension_lt (k : ℕ) (hk : 4 ≤ k) :
    (k + 2).choose 2 < k * k := by
  have hmul : 4 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have hquad : 3 * k + 2 < k * k := by omega
  have hnum : (k + 2) * (k + 1) < 2 * (k * k) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega
  rw [Nat.choose_two_right]
  have hsub : k + 2 - 1 = k + 1 := by omega
  rw [hsub]
  omega

end Nagata.Workers.W24

end

section

/-! Scalar-image algebra of the square coefficient contradiction. -/
namespace Nagata.Workers.W24

/-- Nonzero scalar multiplication preserves being outside a linear image. -/
theorem nonzero_smul_outside_range {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (c : W) (hc : c ∉ f.range) (a : K) (ha : a ≠ 0) :
    a • c ∉ f.range := by
  intro h
  exact hc ((f.range.smul_mem_iff ha).mp h)

/-- This is the final evaluation-map contradiction once the coefficient identity
and a nonzero scalar have been supplied by the geometric construction. -/
theorem evaluation_coefficient_contradiction {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (c : W) (hc : c ∉ f.range) (a : K) (ha : a ≠ 0)
    (s : V) (heq : f s = a • c) : False := by
  apply nonzero_smul_outside_range f c hc a ha
  exact ⟨s, heq⟩

end Nagata.Workers.W24

end

section

/-! The actual highest normal coefficient modulo a possibly reducible equation.
No domain structure on the quotient is assumed. -/
noncomputable section
namespace Nagata.Workers.W24
open Polynomial

/-- Polynomial of residue classes along the principal equation G. -/
def normalResiduePolynomial {A : Type*} [CommRing A] (G : A) (F : A[X]) :
    Polynomial (A ⧸ Ideal.span ({G} : Set A)) :=
  F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set A)))

/-- Above the genuine quotient-polynomial degree, every lift coefficient is
G-divisible and therefore restricts to zero on every component. -/
theorem above_normalResidue_degree_dvd {A : Type*} [CommRing A]
    (G : A) (F : A[X]) (j : ℕ) (hj : (normalResiduePolynomial G F).natDegree < j) :
    G ∣ F.coeff j := by
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt hj
  rw [normalResiduePolynomial, Polynomial.coeff_map] at hz
  exact (Ideal.Quotient.eq_zero_iff_dvd G (F.coeff j)).mp hz

/-- The highest genuine residue coefficient is not G-divisible. -/
theorem top_normalResidue_coefficient_not_dvd {A : Type*} [CommRing A]
    (G : A) (F : A[X]) (hne : normalResiduePolynomial G F ≠ 0) :
    ¬ G ∣ F.coeff (normalResiduePolynomial G F).natDegree := by
  intro hdiv
  have hz := (Ideal.Quotient.eq_zero_iff_dvd G _).mpr hdiv
  have hcoeff : (normalResiduePolynomial G F).coeff
      (normalResiduePolynomial G F).natDegree = 0 := by
    simpa only [normalResiduePolynomial, Polynomial.coeff_map] using hz
  exact (Polynomial.leadingCoeff_ne_zero.mpr hne) hcoeff

/-- Any ring restriction killing G has degree bounded by the top residue index. -/
theorem restriction_natDegree_le_normalResidue_degree {A B : Type*}
    [CommRing A] [CommRing B] (G : A) (F : A[X]) (f : A →+* B) (hG : f G = 0) :
    (F.map f).natDegree ≤ (normalResiduePolynomial G F).natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  obtain ⟨q, hq⟩ := above_normalResidue_degree_dvd G F j hj
  rw [Polynomial.coeff_map, hq, map_mul, hG, zero_mul]

end Nagata.Workers.W24

end
end

section

namespace Nagata.Workers.W24

/-- The degree comparison for the leading coefficient of a normal polynomial. -/
theorem leadingCoefficient_degree_le (k d m j : Nat) (hd : d ≤ k * m) :
    k * (d - k * j) ≤ k * k * (m - j) := by
  have h := Nat.mul_le_mul_left k (Nat.sub_le_sub_right hd (k * j))
  simpa [Nat.mul_sub_left_distrib, Nat.mul_assoc] using h

/-- Strict degree deficit excludes the prescribed number of zeros, numerically. -/
theorem leadingCoefficient_degree_lt (k d m j : Nat) (hk : 0 < k)
    (hd : d < k * m) (hdj : k * j ≤ d) :
    k * (d - k * j) < k * k * (m - j) := by
  have hsub : d - k * j < k * m - k * j := by omega
  have h := Nat.mul_lt_mul_of_pos_left hsub hk
  simpa [Nat.mul_sub_left_distrib, Nat.mul_assoc] using h

/-- Equality of the two degree bounds forces equality in the original slope. -/
theorem leadingCoefficient_equality_forces_slope (k d m j : Nat)
    (hk : 0 < k) (hd : d ≤ k * m) (hdj : k * j ≤ d)
    (heq : k * (d - k * j) = k * k * (m - j)) : d = k * m := by
  have hnlt : ¬ d < k * m := by
    intro hlt
    have h := leadingCoefficient_degree_lt k d m j hk hlt hdj
    omega
  omega

/-- The index bound used before splitting the square-case argument. -/
theorem leadingIndex_le_m (k d m j : Nat) (hk : 0 < k)
    (hdj : k * j ≤ d) (hd : d ≤ k * m) : j ≤ m := by
  apply Nat.le_of_not_gt
  intro hmj
  have hmul := Nat.mul_lt_mul_of_pos_left hmj hk
  omega

/-- At the last possible index, the coefficient exponent is zero. -/
theorem lastIndex_exponent_zero (k d m : Nat)
    (hmd : k * m ≤ d) (hdm : d ≤ k * m) : d = k * m ∧ d - k * m = 0 := by
  omega

/-- The previous coefficient then has the normal bundle's exponent. -/
theorem penultimate_exponent (k m : Nat) (hm : 0 < m) :
    k * m - k * (m - 1) = k := by
  have hm' : m = (m - 1) + 1 := by omega
  calc
    k * m - k * (m - 1) = k * ((m - 1) + 1) - k * (m - 1) := by rw [← hm']
    _ = k := by simp [Nat.mul_add]

/-- A positive power is obtained in the lower-index branch. -/
theorem lowerIndex_positive_power (m j : Nat) (hj : j < m) : 0 < m - j := by
  omega

/-- Twice the section-space dimension is strictly less than twice k². -/
theorem twice_sectionDimension_lt (k : Nat) (hk : 4 ≤ k) :
    k * k + 3 * k < 2 * (k * k) := by
  have hkpos : 0 < k := by omega
  have h3k : 3 < k := by omega
  have hmul := Nat.mul_lt_mul_of_pos_right h3k hkpos
  omega

/-- Integer form of (k²+3k)/2 < k² for the square case. -/
theorem sectionDimension_lt (k : Nat) (hk : 4 ≤ k) :
    (k * k + 3 * k) / 2 < k * k := by
  have h := twice_sectionDimension_lt k hk
  omega

/-- Positivity of the plane-curve genus formula in the square range. -/
theorem genusFormula_pos (k : Nat) (hk : 4 ≤ k) :
    0 < ((k - 1) * (k - 2)) / 2 := by
  have ha : 3 ≤ k - 1 := by omega
  have hb : 2 ≤ k - 2 := by omega
  have h := Nat.mul_le_mul ha hb
  omega

end Nagata.Workers.W24

end

section

/-! Actual one-variable polynomial statements for the last step of `prop:squares`.
Divisibility is the polynomial expression of the fiber multiplicity condition. -/
namespace Nagata.Workers.W24
open Polynomial

/-- A degree-at-most-m polynomial divisible by (X-c)^m has the required shape. -/
theorem polynomial_eq_leadingCoeff_mul_power {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (c : R) (m : Nat) (hd : p.natDegree ≤ m)
    (hmult : (X - C c) ^ m ∣ p) :
    p = C p.leadingCoeff * (X - C c) ^ m := by
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    ((monic_X_sub_C c).pow m) hmult
  simpa only [(monic_X_sub_C c).natDegree_pow, natDegree_X_sub_C, mul_one] using hd

/-- The coefficient of X^(m-1) in the translated monic power. -/
theorem power_penultimate_coefficient {R : Type*} [CommRing R] [Nontrivial R]
    (c : R) (m : Nat) (hm : 0 < m) :
    ((X - C c) ^ m).coeff (m - 1) = -((m : R) * c) := by
  have hdeg : ((X - C c) ^ m).natDegree = m := by
    rw [(monic_X_sub_C c).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hnext := (monic_X_sub_C c).nextCoeff_pow m
  rw [nextCoeff_of_natDegree_pos (by rw [hdeg]; exact hm), hdeg,
    nextCoeff_X_sub_C] at hnext
  simpa only [nsmul_eq_mul, mul_neg] using hnext

/-- Coefficient comparison for the actual polynomial, retaining its leading scalar. -/
theorem polynomial_penultimate_coefficient {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (c : R) (m : Nat) (hm : 0 < m) (hd : p.natDegree ≤ m)
    (hmult : (X - C c) ^ m ∣ p) :
    p.coeff (m - 1) = p.leadingCoeff * (-((m : R) * c)) := by
  have heq := polynomial_eq_leadingCoeff_mul_power p c m hd hmult
  have hcoeff := congrArg (fun q : R[X] => q.coeff (m - 1)) heq
  simpa only [coeff_C_mul, power_penultimate_coefficient c m hm] using hcoeff

/-- The source manuscript's scalar-times-fiber-vector coefficient form. -/
theorem polynomial_penultimate_coefficient_scalar {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (c : R) (m : Nat) (hm : 0 < m) (hd : p.natDegree ≤ m)
    (hmult : (X - C c) ^ m ∣ p) :
    p.coeff (m - 1) = (-(m : R) * p.leadingCoeff) * c := by
  rw [polynomial_penultimate_coefficient p c m hm hd hmult]
  simp only [mul_neg, neg_mul, mul_assoc]
  rw [mul_left_comm]

/-- The multiplying scalar in characteristic zero is nonzero. -/
theorem coefficient_scalar_ne_zero {K : Type*} [Field K] [CharZero K]
    (p : K[X]) (hp : p ≠ 0) (m : Nat) (hm : 0 < m) :
    -(m : K) * p.leadingCoeff ≠ 0 := by
  exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)))
    (leadingCoeff_ne_zero.mpr hp)

/-- The same coefficient identity from mathlib's genuine root multiplicity. -/
theorem rootMultiplicity_penultimate_coefficient {R : Type*} [CommRing R]
    [Nontrivial R] (p : R[X]) (hp : p ≠ 0) (c : R) (m : Nat) (hm : 0 < m)
    (hd : p.natDegree ≤ m) (hmult : m ≤ p.rootMultiplicity c) :
    p.coeff (m - 1) = (-(m : R) * p.leadingCoeff) * c := by
  exact polynomial_penultimate_coefficient_scalar p c m hm hd
    ((le_rootMultiplicity_iff hp).mp hmult)

end Nagata.Workers.W24

end

section

/-!
Actual restricted homogeneous polynomial functions for the square argument.
These retain precisely the homogeneous lifts produced in §1's normal-polynomial
construction. We do not identify this space with every global section of a
line bundle; that stronger identification is unnecessary for these lifts.
Projective sheaf descent is a separate geometric interface.
-/
noncomputable section
namespace Nagata.Workers.W24
open MvPolynomial

/-- Nonzero homogeneous coordinate vectors on the actual equation G=0. -/
abbrev ConePoint (G : MvPolynomial (Fin 3) ℂ) :=
  {v : Fin 3 → ℂ // v ≠ 0 ∧ MvPolynomial.eval v G = 0}

/-- The ordinary vector space of homogeneous plane forms of degree n. -/
abbrev PlaneForms (n : Nat) := MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n

/-- Simultaneous evaluation of actual homogeneous forms at chosen coordinates. -/
def homogeneousEvaluation {ι : Type*} (n : Nat) (a : ι → Fin 3 → ℂ) :
    PlaneForms n →ₗ[ℂ] (ι → ℂ) :=
  LinearMap.pi fun i => ((MvPolynomial.aeval (a i)).toLinearMap).comp
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n).subtype

@[simp] theorem homogeneousEvaluation_apply {ι : Type*} (n : Nat)
    (a : ι → Fin 3 → ℂ) (F : PlaneForms n) (i : ι) :
    homogeneousEvaluation n a F i = MvPolynomial.eval (a i) F.val := rfl

/-- Restricted polynomial functions on the punctured affine cone of G.
The source construction lands in this genuine image submodule. -/
def restrictedPolynomialFunctions (G : MvPolynomial (Fin 3) ℂ) (n : Nat) :
    Submodule ℂ (ConePoint G → ℂ) :=
  (homogeneousEvaluation n (fun a : ConePoint G => a.val)).range

/-- Every actual homogeneous lift has the standard degree-n scaling law. -/
theorem homogeneousEvaluation_scale {ι : Type*} (n : Nat)
    (a : ι → Fin 3 → ℂ) (u : ι → ℂ) (F : PlaneForms n) (i : ι) :
    homogeneousEvaluation n (fun i j => u i * a i j) F i =
      (u i) ^ n * homogeneousEvaluation n a F i := by
  exact Nagata.W16.homogeneous_eval_scale F.property (a i) (u i)

/-- The curve equation itself is an element of its degree's homogeneous space. -/
def equationForm {k : Nat} (G : Nagata.W16.NonzeroHomogeneousForm k) : PlaneForms k :=
  ⟨G.polynomial, G.homogeneous⟩

/-- A nonzero curve equation supplies a genuinely nonzero kernel vector. -/
theorem equationForm_ne_zero {k : Nat} (G : Nagata.W16.NonzeroHomogeneousForm k) :
    equationForm G ≠ 0 := by
  intro h
  exact G.nonzero (congrArg Subtype.val h)

/-- Evaluation of the equation is zero at every selected point on its cone. -/
theorem equationForm_in_evaluation_kernel {ι : Type*} {k : Nat}
    (G : Nagata.W16.NonzeroHomogeneousForm k) (a : ι → ConePoint G.polynomial) :
    equationForm G ∈ (homogeneousEvaluation k (fun i => (a i).val)).ker := by
  change homogeneousEvaluation k (fun i => (a i).val) (equationForm G) = 0
  funext i
  exact (a i).property.2

/-- Degree-zero homogeneous plane forms are actual constants. -/
theorem degreeZeroForm_eq_constant (F : PlaneForms 0) :
    F.val = MvPolynomial.C (F.val.coeff 0) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr F.property

/-- The leading coefficient's common scalar follows from its actual degree-zero
lift, without a general theorem about all global functions on a projective curve. -/
theorem degreeZeroForm_evaluation_constant {ι : Type*} (a : ι → Fin 3 → ℂ)
    (F : PlaneForms 0) (i : ι) :
    homogeneousEvaluation 0 a F i = F.val.coeff 0 := by
  rw [homogeneousEvaluation_apply, degreeZeroForm_eq_constant]
  simp

/-- A nonzero degree-zero lift gives a nonzero common scalar. -/
theorem degreeZeroForm_constant_ne_zero (F : PlaneForms 0) (hF : F ≠ 0) :
    F.val.coeff 0 ≠ 0 := by
  intro h
  apply hF
  apply Subtype.ext
  rw [degreeZeroForm_eq_constant, h, MvPolynomial.C_0]
  rfl

end Nagata.Workers.W24

end
end

section

namespace Nagata.Workers.W24

open Module

/-- A genuine linear map with smaller domain dimension misses a vector. -/
theorem exists_vector_outside_range {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    (hdim : finrank K V < finrank K W) : ∃ c : W, c ∉ f.range := by
  classical
  have hsurj : ¬ Function.Surjective f := by
    intro hs
    have hle := f.finrank_range_le
    rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hle
    exact (not_lt_of_ge hle) hdim
  simpa only [Function.Surjective, LinearMap.mem_range, not_forall] using hsurj

end Nagata.Workers.W24

end

end OAI
