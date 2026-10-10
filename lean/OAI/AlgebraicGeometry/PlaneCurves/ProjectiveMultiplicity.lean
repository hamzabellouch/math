import OAI.AlgebraicGeometry.PlaneCurves.ChartMultiplicityBridge
import OAI.AlgebraicGeometry.PlaneCurves.TaylorMultiplicity

namespace OAI

/-!
# Ordinary projective multiplicity of homogeneous equations; Homogeneous equations up to scalar association
-/

section

/-!
# Projective classes of nonzero homogeneous plane equations

The parameter space is the actual projectivization of the vector space of
degree-`d` homogeneous ternary complex polynomials. Equations are identified
only by nonzero constant multiples, not by equality of their zero sets. Thus
nonreduced equations retain their principal ideals and their local orders.
-/

noncomputable section

namespace Nagata.W16

open Nagata.ProjectiveGeometry

abbrev HomogeneousFormSpace (d : ℕ) :=
  ↥(MvPolynomial.homogeneousSubmodule (Fin 3) ℂ d)

/-- Nonzero homogeneous equations modulo nonzero complex scalar. -/
abbrev PlaneEquationClass (d : ℕ) := Projectivization ℂ (HomogeneousFormSpace d)

/-- A positive-degree equation class. The Cartier-divisor correspondence is
not included as a structure field or an assumption. -/
structure PositivePlaneEquation where
  degree : ℕ
  degree_pos : 0 < degree
  equationClass : PlaneEquationClass degree

def formVector {d : ℕ} (F : NonzeroHomogeneousForm d) : HomogeneousFormSpace d :=
  ⟨F.polynomial, F.homogeneous⟩

theorem formVector_ne_zero {d : ℕ} (F : NonzeroHomogeneousForm d) : formVector F ≠ 0 := by
  intro h
  exact F.nonzero (congrArg Subtype.val h)

def classOfForm {d : ℕ} (F : NonzeroHomogeneousForm d) : PlaneEquationClass d :=
  Projectivization.mk ℂ (formVector F) (formVector_ne_zero F)

def classRepresentative {d : ℕ} (C : PlaneEquationClass d) : NonzeroHomogeneousForm d where
  polynomial := C.rep.val
  homogeneous := C.rep.property
  nonzero := by
    intro h
    apply C.rep_nonzero
    exact Subtype.ext h

theorem classOfForm_representative {d : ℕ} (C : PlaneEquationClass d) :
    classOfForm (classRepresentative C) = C := by
  exact Projectivization.mk_rep C

theorem classOfForm_surjective (d : ℕ) :
    Function.Surjective (classOfForm : NonzeroHomogeneousForm d → PlaneEquationClass d) := by
  intro C
  exact ⟨classRepresentative C, classOfForm_representative C⟩

/-- This equality criterion identifies equations only by units of `ℂ`. -/
theorem classOfForm_eq_iff {d : ℕ} (F G : NonzeroHomogeneousForm d) :
    classOfForm F = classOfForm G ↔
      ∃ a : ℂˣ, MvPolynomial.C (a : ℂ) * G.polynomial = F.polynomial := by
  unfold classOfForm
  rw [Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h := congrArg (fun v : HomogeneousFormSpace d => v.val) ha
    simpa [formVector, Units.smul_def, MvPolynomial.smul_eq_C_mul] using h
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    simpa [formVector, Units.smul_def, MvPolynomial.smul_eq_C_mul] using ha

theorem representative_classOfForm {d : ℕ} (F : NonzeroHomogeneousForm d) :
    ∃ a : ℂˣ, MvPolynomial.C (a : ℂ) * F.polynomial =
      (classRepresentative (classOfForm F)).polynomial := by
  obtain ⟨a, ha⟩ :=
    Projectivization.exists_smul_eq_mk_rep ℂ (formVector F) (formVector_ne_zero F)
  refine ⟨a, ?_⟩
  have h := congrArg (fun v : HomogeneousFormSpace d => v.val) ha
  simpa [classOfForm, classRepresentative, formVector, Units.smul_def,
    MvPolynomial.smul_eq_C_mul] using h

theorem representative_totalDegree {d : ℕ} (C : PlaneEquationClass d) :
    (classRepresentative C).polynomial.totalDegree = d :=
  (classRepresentative C).totalDegree_eq

/-- The local-order lower bound of an equation class, using the actual chart
coordinate rings and their point maximal ideals. -/
def classMultiplicityAtLeast {d : ℕ} (C : PlaneEquationClass d)
    (p : PlanePoint) (m : ℕ) : Prop :=
  multiplicityAtLeast (classRepresentative C).polynomial p m

theorem classMultiplicityAtLeast_classOfForm {d : ℕ}
    (F : NonzeroHomogeneousForm d) (p : PlanePoint) (m : ℕ) :
    classMultiplicityAtLeast (classOfForm F) p m ↔ multiplicityAtLeast F.polynomial p m := by
  obtain ⟨a, ha⟩ := representative_classOfForm F
  unfold classMultiplicityAtLeast
  rw [← ha]
  exact multiplicityAtLeast_C_mul_iff (a : ℂ) a.ne_zero F.polynomial p m

theorem classMultiplicityAtLeast_iff_localOrder {d : ℕ}
    (C : PlaneEquationClass d) (p : PlanePoint) (m : ℕ) :
    classMultiplicityAtLeast C p m ↔ ∀ c : Fin 3, p.rep c ≠ 0 →
      AffineMultiplicity.localOrderAtLeast (chartCoordinates c p) m
        (dehomogenize c (classRepresentative C).polynomial) :=
  multiplicityAtLeast_iff_localOrder _ p m

/-- The underlying projective zero locus is kept separately from the equation
class: it is not the equivalence relation defining the class. -/
def classZeroLocus {d : ℕ} (C : PlaneEquationClass d) : Set PlanePoint :=
  {p | MvPolynomial.eval p.rep (classRepresentative C).polynomial = 0}

theorem classZeroLocus_classOfForm {d : ℕ} (F : NonzeroHomogeneousForm d) (p : PlanePoint) :
    p ∈ classZeroLocus (classOfForm F) ↔ MvPolynomial.eval p.rep F.polynomial = 0 := by
  obtain ⟨a, ha⟩ := representative_classOfForm F
  change MvPolynomial.eval p.rep (classRepresentative (classOfForm F)).polynomial = 0 ↔ _
  rw [← ha, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  simp [a.ne_zero]

theorem mem_classZeroLocus_iff_order_one {d : ℕ} (C : PlaneEquationClass d) (p : PlanePoint) :
    p ∈ classZeroLocus C ↔ classMultiplicityAtLeast C p 1 :=
  (multiplicityAtLeast_one_iff (classRepresentative C).homogeneous p).symm

/-- The full principal ideal of the local equation, without radicalization.
In particular, powers of equations retain their nonreduced structure. -/
def classChartIdeal {d : ℕ} (C : PlaneEquationClass d) (c : Fin 3) :
    Ideal (MvPolynomial (ChartVariables c) ℂ) :=
  Ideal.span {dehomogenize c (classRepresentative C).polynomial}

theorem classChartIdeal_classOfForm {d : ℕ} (F : NonzeroHomogeneousForm d) (c : Fin 3) :
    classChartIdeal (classOfForm F) c = Ideal.span {dehomogenize c F.polynomial} := by
  obtain ⟨a, ha⟩ := representative_classOfForm F
  unfold classChartIdeal
  rw [← ha, dehomogenize_mul, dehomogenize_C]
  exact Ideal.span_singleton_mul_left_unit (a.isUnit.map MvPolynomial.C) _

/-- The chart equation is nonzero, so its ideal defines a genuine principal
hypersurface equation, including its multiplicity structure. -/
theorem classChartEquation_ne_zero {d : ℕ} (C : PlaneEquationClass d) (c : Fin 3) :
    dehomogenize c (classRepresentative C).polynomial ≠ 0 :=
  dehomogenize_ne_zero (classRepresentative C).homogeneous (classRepresentative C).nonzero c

/-- The full chart ideal of a product is the product of its chart ideals. -/
theorem classChartIdeal_mul {d e : ℕ} (F : NonzeroHomogeneousForm d)
    (G : NonzeroHomogeneousForm e) (c : Fin 3) :
    classChartIdeal (classOfForm (F.mul G)) c =
      classChartIdeal (classOfForm F) c * classChartIdeal (classOfForm G) c := by
  rw [classChartIdeal_classOfForm, classChartIdeal_classOfForm, classChartIdeal_classOfForm]
  change Ideal.span {dehomogenize c (F.polynomial * G.polynomial)} = _
  rw [dehomogenize_mul, Ideal.span_singleton_mul_span_singleton]

/-- Raising an equation to the `N`th power raises its actual principal chart
ideal to the `N`th power. This explicitly preserves nonreduced structure. -/
theorem classChartIdeal_pow {d : ℕ} (F : NonzeroHomogeneousForm d)
    (c : Fin 3) (N : ℕ) :
    classChartIdeal (classOfForm (F.pow N)) c = classChartIdeal (classOfForm F) c ^ N := by
  rw [classChartIdeal_classOfForm, classChartIdeal_classOfForm]
  change Ideal.span {dehomogenize c (F.polynomial ^ N)} = _
  rw [dehomogenize_pow, Ideal.span_singleton_pow]

/-- The full principal chart ideals agree after transport into the actual
local ring at a point of an overlap. The transition factor is a proved unit. -/
theorem classChartIdeal_local_compatibility {d : ℕ} (C : PlaneEquationClass d)
    (b c : Fin 3) (p : PlanePoint) (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    Ideal.map (chartTransitionToLocalRing b c p hb hc) (classChartIdeal C c) =
      Ideal.map
        (algebraMap (MvPolynomial (ChartVariables b) ℂ) (ChartLocalRing b p))
        (classChartIdeal C b) := by
  simp only [classChartIdeal, Ideal.map_span, Set.image_singleton]
  rw [chartTransition_dehomogenize (classRepresentative C).homogeneous b c p hb hc]
  exact Ideal.span_singleton_mul_left_unit
    (((localChartDenominatorUnit b c p hb hc)⁻¹).isUnit.pow d) _

end Nagata.W16

end
end

section

/-! # Numerical ordinary multiplicity on the genuine projective plane

The number is the minimum nonzero Taylor degree in an actual affine chart.
The chart transport theorem proves it is independent of the chosen containing
chart. It does not encode any degree bound or Nagata inequality.
-/

noncomputable section

namespace Nagata.ProjectiveGeometry

def formOrdinaryMultiplicity {d : ℕ} (F : W16.NonzeroHomogeneousForm d)
    (p : PlanePoint) : ℕ :=
  let c := Classical.choose (chart_exists p)
  AffineMultiplicity.ordinaryMultiplicity (chartCoordinates c p)
    (dehomogenize c F.polynomial)
    (W16.dehomogenize_ne_zero F.homogeneous F.nonzero c)

theorem multiplicityAtLeast_iff_le_formOrdinaryMultiplicity {d : ℕ}
    (F : W16.NonzeroHomogeneousForm d) (p : PlanePoint) (m : ℕ) :
    multiplicityAtLeast F.polynomial p m ↔ m ≤ formOrdinaryMultiplicity F p := by
  let c := Classical.choose (chart_exists p)
  have hc : p.rep c ≠ 0 := Classical.choose_spec (chart_exists p)
  exact (multiplicityAtLeast_iff_chart F.homogeneous p c hc m).trans
    (AffineMultiplicity.orderAtLeast_iff_le_ordinaryMultiplicity
      (chartCoordinates c p) m (dehomogenize c F.polynomial)
      (W16.dehomogenize_ne_zero F.homogeneous F.nonzero c))

theorem formOrdinaryMultiplicity_eq_chart {d : ℕ}
    (F : W16.NonzeroHomogeneousForm d) (p : PlanePoint)
    (c : Fin 3) (hc : p.rep c ≠ 0) :
    formOrdinaryMultiplicity F p =
      AffineMultiplicity.ordinaryMultiplicity (chartCoordinates c p)
        (dehomogenize c F.polynomial)
        (W16.dehomogenize_ne_zero F.homogeneous F.nonzero c) := by
  apply Nat.le_antisymm
  · apply (AffineMultiplicity.orderAtLeast_iff_le_ordinaryMultiplicity
      (chartCoordinates c p) _ (dehomogenize c F.polynomial)
      (W16.dehomogenize_ne_zero F.homogeneous F.nonzero c)).mp
    apply (multiplicityAtLeast_iff_chart F.homogeneous p c hc _).mp
    exact (multiplicityAtLeast_iff_le_formOrdinaryMultiplicity F p _).mpr le_rfl
  · apply (multiplicityAtLeast_iff_le_formOrdinaryMultiplicity F p _).mp
    apply (multiplicityAtLeast_iff_chart F.homogeneous p c hc _).mpr
    exact AffineMultiplicity.orderAtLeast_ordinaryMultiplicity
      (chartCoordinates c p) (dehomogenize c F.polynomial)
      (W16.dehomogenize_ne_zero F.homogeneous F.nonzero c)

theorem formOrdinaryMultiplicity_attained {d : ℕ}
    (F : W16.NonzeroHomogeneousForm d) (p : PlanePoint)
    (c : Fin 3) (hc : p.rep c ≠ 0) :
    ∃ a : ChartVariables c →₀ ℕ,
      (AffineMultiplicity.translateHom (chartCoordinates c p)
        (dehomogenize c F.polynomial)).coeff a ≠ 0 ∧
      formOrdinaryMultiplicity F p = Finsupp.degree a := by
  rw [formOrdinaryMultiplicity_eq_chart F p c hc]
  exact AffineMultiplicity.ordinaryMultiplicity_attained
    (chartCoordinates c p) (dehomogenize c F.polynomial)
    (W16.dehomogenize_ne_zero F.homogeneous F.nonzero c)

def classOrdinaryMultiplicity {d : ℕ} (C : W16.PlaneEquationClass d)
    (p : PlanePoint) : ℕ := formOrdinaryMultiplicity (W16.classRepresentative C) p

theorem classMultiplicityAtLeast_iff_le_classOrdinaryMultiplicity {d : ℕ}
    (C : W16.PlaneEquationClass d) (p : PlanePoint) (m : ℕ) :
    W16.classMultiplicityAtLeast C p m ↔ m ≤ classOrdinaryMultiplicity C p :=
  multiplicityAtLeast_iff_le_formOrdinaryMultiplicity (W16.classRepresentative C) p m

theorem classOrdinaryMultiplicity_classOfForm {d : ℕ}
    (F : W16.NonzeroHomogeneousForm d) (p : PlanePoint) :
    classOrdinaryMultiplicity (W16.classOfForm F) p = formOrdinaryMultiplicity F p := by
  apply Nat.le_antisymm
  · apply (multiplicityAtLeast_iff_le_formOrdinaryMultiplicity F p _).mp
    apply (W16.classMultiplicityAtLeast_classOfForm F p _).mp
    exact (classMultiplicityAtLeast_iff_le_classOrdinaryMultiplicity _ p _).mpr le_rfl
  · apply (classMultiplicityAtLeast_iff_le_classOrdinaryMultiplicity _ p _).mp
    apply (W16.classMultiplicityAtLeast_classOfForm F p _).mpr
    exact (multiplicityAtLeast_iff_le_formOrdinaryMultiplicity F p _).mpr le_rfl

end Nagata.ProjectiveGeometry

end
end

end OAI
