import OAI.AlgebraicGeometry.PlaneCurves.IdealCycles
import OAI.AlgebraicGeometry.PlaneCurves.ProjectiveMultiplicity

namespace OAI

/-!
# Effective cycles, their equations, and equation-independent degrees
-/

section

/-! Exact compatibility between polynomial associates, prime-ideal cycles,
and projective classes of homogeneous equations. -/
noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16 MvPolynomial

/-- Every polynomial unit over C is exactly a nonzero constant scalar. -/
theorem ternary_unit_eq_C (u : TernaryPolynomialˣ) :
    ∃ a : ℂˣ, (u : TernaryPolynomial) = MvPolynomial.C (a : ℂ) := by
  have hu := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (unit_polynomial_totalDegree u)
  have ha : (u : TernaryPolynomial).coeff 0 ≠ 0 := by
    intro hz
    apply u.ne_zero
    rw [hu, hz, MvPolynomial.C_0]
  exact ⟨Units.mk0 _ ha, hu⟩

/-- Association is precisely equality up to nonzero complex scalar, including
for reducible and nonreduced polynomials. -/
theorem associated_iff_complex_unit (F G : TernaryPolynomial) :
    Associated F G ↔ ∃ a : ℂˣ, MvPolynomial.C (a : ℂ) * G = F := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.symm
    obtain ⟨a, ha⟩ := ternary_unit_eq_C u
    exact ⟨a, by simpa only [ha, mul_comm] using hu⟩
  · rintro ⟨a, rfl⟩
    exact associated_unit_mul_left G (MvPolynomial.C (a : ℂ)) (a.isUnit.map MvPolynomial.C)

/-- Associated nonzero equations have equal actual total degrees. -/
theorem associated_totalDegree_eq {F G : TernaryPolynomial} (hF : F ≠ 0)
    (h : Associated F G) : F.totalDegree = G.totalDegree := by
  obtain ⟨u, rfl⟩ := h
  rw [MvPolynomial.totalDegree_mul_of_isDomain hF u.ne_zero, unit_polynomial_totalDegree, add_zero]

/-- The full ideal cycle identifies exactly the projective equation class at a
fixed degree, not merely the underlying set of zeros. -/
theorem classOfForm_eq_iff_idealCycle {d : ℕ} (F G : NonzeroHomogeneousForm d) :
    classOfForm F = classOfForm G ↔ equationIdealCycle F.polynomial = equationIdealCycle G.polynomial := by
  rw [classOfForm_eq_iff, equationIdealCycle_eq_iff F.nonzero G.nonzero,
    associated_iff_complex_unit]

end Nagata.Workers.W10

end
end

section

noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16 MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero finite effective cycle of genuine homogeneous prime principal
ideals in C[X0,X1,X2]. The weights retain repeated components. -/
def EffectivePlaneCurve := {D : Ideal TernaryPolynomial →₀ ℕ //
  D ≠ 0 ∧ ∀ I ∈ D.support, I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal ∧
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)}

/-- Reconstruct an actual homogeneous equation from the ideal cycle. -/
def curveEquation (C : EffectivePlaneCurve) : TernaryPolynomial :=
  Classical.choose (exists_positive_degree_equation_of_homogeneous_cycle C.val C.property.1 C.property.2)

theorem curveEquation_spec (C : EffectivePlaneCurve) :
    curveEquation C ≠ 0 ∧ (curveEquation C).IsHomogeneous (curveEquation C).totalDegree ∧
      0 < (curveEquation C).totalDegree ∧ equationIdealCycle (curveEquation C) = C.val :=
  Classical.choose_spec (exists_positive_degree_equation_of_homogeneous_cycle C.val C.property.1 C.property.2)

theorem curveEquation_nonzero (C : EffectivePlaneCurve) : curveEquation C ≠ 0 :=
  (curveEquation_spec C).1

def curveDegree (C : EffectivePlaneCurve) : ℕ := (curveEquation C).totalDegree

theorem curveDegree_pos (C : EffectivePlaneCurve) : 0 < curveDegree C :=
  (curveEquation_spec C).2.2.1

theorem curveEquation_homogeneous (C : EffectivePlaneCurve) :
    (curveEquation C).IsHomogeneous (curveDegree C) := (curveEquation_spec C).2.1

@[simp] theorem curveEquation_idealCycle (C : EffectivePlaneCurve) :
    equationIdealCycle (curveEquation C) = C.val := (curveEquation_spec C).2.2.2

/-- The chosen reconstruction is packaged as a genuine nonzero homogeneous form. -/
def curveForm (C : EffectivePlaneCurve) : NonzeroHomogeneousForm (curveDegree C) :=
  ⟨curveEquation C, curveEquation_homogeneous C, curveEquation_nonzero C⟩

def curveEquationClass (C : EffectivePlaneCurve) : PositivePlaneEquation :=
  ⟨curveDegree C, curveDegree_pos C, classOfForm (curveForm C)⟩

/-- Replacing a form by the chosen representative of its projective class
preserves the entire ideal cycle, including every repeated-factor weight. -/
theorem equationIdealCycle_classRepresentative {d : ℕ} (F : NonzeroHomogeneousForm d) :
    equationIdealCycle (classRepresentative (classOfForm F)).polynomial = equationIdealCycle F.polynomial :=
  (classOfForm_eq_iff_idealCycle _ _).mp (classOfForm_representative (classOfForm F))

/-- An actual positive-degree projective equation class gives its zero-divisor cycle. -/
def curveOfEquation (E : PositivePlaneEquation) : EffectivePlaneCurve :=
  ⟨equationIdealCycle (classRepresentative E.equationClass).polynomial, by
    constructor
    · intro hzero
      obtain ⟨u, hu⟩ := (equationIdealCycle_zero_iff (classRepresentative E.equationClass).nonzero).mp hzero
      have hd0 : (classRepresentative E.equationClass).polynomial.totalDegree = 0 := by
        rw [← hu]
        exact unit_polynomial_totalDegree u
      exact (Nat.ne_of_gt E.degree_pos) ((representative_totalDegree E.equationClass).symm.trans hd0)
    · intro I hI
      have hp := equationIdealCycle_support _ hI
      exact ⟨hp.1, hp.2.1, hp.2.2,
        equationIdealCycle_homogeneous (classRepresentative E.equationClass).nonzero
          (classRepresentative E.equationClass).homogeneous hI⟩⟩

@[simp] theorem curveOfEquation_curveEquationClass (C : EffectivePlaneCurve) :
    curveOfEquation (curveEquationClass C) = C := by
  apply Subtype.ext
  change equationIdealCycle (classRepresentative (classOfForm (curveForm C))).polynomial = C.val
  rw [equationIdealCycle_classRepresentative]
  exact curveEquation_idealCycle C

/-- Even across degrees, equal ideal cycles identify precisely the same positive
projective equation class. -/
theorem curveOfEquation_injective : Function.Injective curveOfEquation := by
  rintro ⟨d, hd, F⟩ ⟨e, he, G⟩ h
  have hcycle : equationIdealCycle (classRepresentative F).polynomial =
      equationIdealCycle (classRepresentative G).polynomial := congrArg Subtype.val h
  have hassoc := (equationIdealCycle_eq_iff (classRepresentative F).nonzero
    (classRepresentative G).nonzero).mp hcycle
  have hde : d = e := by
    rw [← representative_totalDegree F, ← representative_totalDegree G]
    exact associated_totalDegree_eq (classRepresentative F).nonzero hassoc
  subst e
  have hFG : F = G := by
    calc
      F = classOfForm (classRepresentative F) := (classOfForm_representative F).symm
      _ = classOfForm (classRepresentative G) := (classOfForm_eq_iff_idealCycle _ _).mpr hcycle
      _ = G := classOfForm_representative G
  subst G
  rfl

@[simp] theorem curveEquationClass_curveOfEquation (E : PositivePlaneEquation) :
    curveEquationClass (curveOfEquation E) = E := by
  apply curveOfEquation_injective
  exact curveOfEquation_curveEquationClass (curveOfEquation E)

/-- Full equivalence between genuine positive effective ideal cycles and all
positive-degree projective equation classes. Repeated components are preserved. -/
def planeCurveEquationEquiv : EffectivePlaneCurve ≃ PositivePlaneEquation where
  toFun := curveEquationClass
  invFun := curveOfEquation
  left_inv := curveOfEquation_curveEquationClass
  right_inv := curveEquationClass_curveOfEquation

end Nagata.Workers.W10

end
end

section

noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16 Nagata.ProjectiveGeometry

/-- Any nonzero equation with this full ideal cycle differs from the chosen
equation by an actual nonzero complex scalar. -/
theorem curveEquation_associated (C : EffectivePlaneCurve) {F : TernaryPolynomial}
    (hF : F ≠ 0) (hcycle : equationIdealCycle F = C.val) :
    Associated (curveEquation C) F :=
  (equationIdealCycle_eq_iff (curveEquation_nonzero C) hF).mp
    ((curveEquation_idealCycle C).trans hcycle.symm)

/-- Degree is independent of the equation, without a homogeneity assumption on
the alternate representative (homogeneity follows from its cycle). -/
theorem curveDegree_eq_totalDegree (C : EffectivePlaneCurve) {F : TernaryPolynomial}
    (hF : F ≠ 0) (hcycle : equationIdealCycle F = C.val) :
    curveDegree C = F.totalDegree :=
  associated_totalDegree_eq (curveEquation_nonzero C) (curveEquation_associated C hF hcycle)

/-- Every alternative homogeneous representative has exactly this degree. -/
theorem curveDegree_eq_formDegree (C : EffectivePlaneCurve) {d : ℕ}
    (F : NonzeroHomogeneousForm d) (hcycle : equationIdealCycle F.polynomial = C.val) :
    curveDegree C = d :=
  (curveDegree_eq_totalDegree C F.nonzero hcycle).trans F.totalDegree_eq

/-- Local multiplicity uses the actual affine chart maximal-ideal powers,
equivalently the actual regular local-ring order used by the manuscript. -/
def curveMultiplicityAtLeast (C : EffectivePlaneCurve) (p : PlanePoint) (m : ℕ) : Prop :=
  multiplicityAtLeast (curveEquation C) p m

theorem curveMultiplicityAtLeast_iff_equation (C : EffectivePlaneCurve) {F : TernaryPolynomial}
    (hF : F ≠ 0) (hcycle : equationIdealCycle F = C.val) (p : PlanePoint) (m : ℕ) :
    curveMultiplicityAtLeast C p m ↔ multiplicityAtLeast F p m := by
  obtain ⟨a, ha⟩ := (associated_iff_complex_unit _ _).mp (curveEquation_associated C hF hcycle)
  unfold curveMultiplicityAtLeast
  rw [← ha]
  exact multiplicityAtLeast_C_mul_iff (a : ℂ) a.ne_zero F p m

theorem curveMultiplicityAtLeast_iff_localOrder (C : EffectivePlaneCurve)
    (p : PlanePoint) (m : ℕ) :
    curveMultiplicityAtLeast C p m ↔ ∀ c : Fin 3, p.rep c ≠ 0 →
      AffineMultiplicity.localOrderAtLeast (chartCoordinates c p) m
        (dehomogenize c (curveEquation C)) :=
  multiplicityAtLeast_iff_localOrder _ p m

/-- The genuine principal ideal on every affine plane chart; no radical is taken. -/
def curveChartIdeal (C : EffectivePlaneCurve) (c : Fin 3) :
    Ideal (MvPolynomial (ChartVariables c) ℂ) :=
  Ideal.span {dehomogenize c (curveEquation C)}

theorem curveChartIdeal_eq_equation (C : EffectivePlaneCurve) {F : TernaryPolynomial}
    (hF : F ≠ 0) (hcycle : equationIdealCycle F = C.val) (c : Fin 3) :
    curveChartIdeal C c = Ideal.span {dehomogenize c F} := by
  obtain ⟨a, ha⟩ := (associated_iff_complex_unit _ _).mp (curveEquation_associated C hF hcycle)
  unfold curveChartIdeal
  rw [← ha, dehomogenize_mul, dehomogenize_C]
  exact Ideal.span_singleton_mul_left_unit (a.isUnit.map MvPolynomial.C) _

/-- The reconstructed projective equation class has precisely the cycle's local order. -/
theorem curveEquationClass_multiplicity (C : EffectivePlaneCurve) (p : PlanePoint) (m : ℕ) :
    classMultiplicityAtLeast (curveEquationClass C).equationClass p m ↔
      curveMultiplicityAtLeast C p m :=
  classMultiplicityAtLeast_classOfForm (curveForm C) p m

theorem curveEquationClass_chartIdeal (C : EffectivePlaneCurve) (c : Fin 3) :
    classChartIdeal (curveEquationClass C).equationClass c = curveChartIdeal C c :=
  classChartIdeal_classOfForm (curveForm C) c

@[simp] theorem curveOfEquation_degree (E : PositivePlaneEquation) :
    curveDegree (curveOfEquation E) = E.degree := by
  have he := congrArg PositivePlaneEquation.degree (curveEquationClass_curveOfEquation E)
  exact he

/-- Passing from a positive projective equation class to its cycle preserves
ordinary local multiplicity exactly. -/
theorem curveOfEquation_multiplicity (E : PositivePlaneEquation) (p : PlanePoint) (m : ℕ) :
    curveMultiplicityAtLeast (curveOfEquation E) p m ↔
      classMultiplicityAtLeast E.equationClass p m := by
  exact curveMultiplicityAtLeast_iff_equation (curveOfEquation E)
    (classRepresentative E.equationClass).nonzero rfl p m

end Nagata.Workers.W10

end
end

section

noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16

def curveOfForm {d : ℕ} (F : NonzeroHomogeneousForm d) (hd : 0 < d) : EffectivePlaneCurve :=
  curveOfEquation ⟨d, hd, classOfForm F⟩

@[simp] theorem curveOfForm_cycle {d : ℕ} (F : NonzeroHomogeneousForm d) (hd : 0 < d) :
    (curveOfForm F hd).val = equationIdealCycle F.polynomial :=
  equationIdealCycle_classRepresentative F

@[simp] theorem curveOfForm_degree {d : ℕ} (F : NonzeroHomogeneousForm d) (hd : 0 < d) :
    curveDegree (curveOfForm F hd) = d :=
  curveOfEquation_degree ⟨d, hd, classOfForm F⟩

/-- The product equation represents exactly the sum of effective cycles. -/
theorem curveOfForm_mul_cycle {d e : ℕ} (F : NonzeroHomogeneousForm d)
    (G : NonzeroHomogeneousForm e) (hd : 0 < d) (he : 0 < e) :
    (curveOfForm (F.mul G) (Nat.add_pos_left hd e)).val =
      (curveOfForm F hd).val + (curveOfForm G he).val := by
  simp only [curveOfForm_cycle]
  exact equationIdealCycle_mul F.nonzero G.nonzero

/-- Repeated components retain every multiplicity: a positive power scales the
whole natural-valued cycle, rather than passing to its reduced support. -/
theorem curveOfForm_pow_cycle {d : ℕ} (F : NonzeroHomogeneousForm d)
    (hd : 0 < d) (N : ℕ) (hN : 0 < N) :
    (curveOfForm (F.pow N) (Nat.mul_pos hd hN)).val = N • (curveOfForm F hd).val := by
  simp only [curveOfForm_cycle]
  exact equationIdealCycle_pow F.polynomial N

end Nagata.Workers.W10

end
end

section

/-! An explicit genuine nonempty effective curve example: the coordinate line. -/
noncomputable section
namespace Nagata.Workers.W10
open Nagata.W16

def coordinateLineForm : NonzeroHomogeneousForm 1 :=
  ⟨MvPolynomial.X (0 : Fin 3), MvPolynomial.isHomogeneous_X ℂ _, MvPolynomial.X_ne_zero (0 : Fin 3)⟩

def coordinateLineCurve : EffectivePlaneCurve := curveOfForm coordinateLineForm zero_lt_one

instance effectivePlaneCurveNonempty : Nonempty EffectivePlaneCurve := ⟨coordinateLineCurve⟩

theorem coordinateLineCurve_degree : curveDegree coordinateLineCurve = 1 :=
  curveOfForm_degree coordinateLineForm zero_lt_one

theorem coordinateLineCurve_cycle :
    coordinateLineCurve.val = Nagata.Workers.W30.equationIdealCycle (MvPolynomial.X (0 : Fin 3)) :=
  curveOfForm_cycle coordinateLineForm zero_lt_one

end Nagata.Workers.W10

end
end

end OAI
