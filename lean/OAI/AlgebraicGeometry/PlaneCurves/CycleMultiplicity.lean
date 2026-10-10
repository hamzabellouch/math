import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import OAI.AlgebraicGeometry.PlaneCurves.EffectiveCurves
import OAI.AlgebraicGeometry.PlaneCurves.LineObstructions

namespace OAI

/-!
# Products, cycles, and ordinary multiplicity invariants
-/

section

/-! Polynomial maps pull affine point multiplicity into genuine root powers. -/

namespace Nagata.AffineMultiplicity

variable {σ R : Type*} [CommRing R]

/-- A concrete polynomial substitution preserving evaluation at a marked
point pulls its `m`th ideal power into the `m`th root-factor power. -/
theorem root_power_dvd_of_orderAtLeast
    (p : σ → R) (a : R) (φ : MvPolynomial σ R →+* Polynomial R)
    (hφ : ∀ g, (φ g).eval a = MvPolynomial.eval p g)
    (m : ℕ) (f : MvPolynomial σ R) (hf : orderAtLeast p m f) :
    (Polynomial.X - Polynomial.C a) ^ m ∣ φ f := by
  let J : Ideal (Polynomial R) := Ideal.span {Polynomial.X - Polynomial.C a}
  have hle : pointIdeal p ≤ Ideal.comap φ J := by
    intro g hg
    change φ g ∈ Ideal.span {Polynomial.X - Polynomial.C a}
    rw [Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
    change (φ g).eval a = 0
    rw [hφ]
    exact (pointIdeal_mem_iff p g).mp hg
  have hmem : f ∈ (Ideal.comap φ J) ^ m := Ideal.pow_right_mono hle m hf
  have htarget : φ f ∈ J ^ m := Ideal.le_comap_pow φ m hmem
  simpa only [J, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using htarget

end Nagata.AffineMultiplicity

end

section

namespace Nagata.W04.ReducibleSquare

variable {K : Type*} [Field K]

theorem lineRestriction_eval (i a : K) (F : MvPolynomial (Fin 3) K) :
    (lineRestriction i F).eval a =
      MvPolynomial.eval ![a, i ^ 2 - i * a, 1] F := by
  have h : (Polynomial.evalRingHom a).comp (lineRestriction i) =
      MvPolynomial.eval ![a, i ^ 2 - i * a, 1] := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [lineRestriction]
    · intro j
      fin_cases j <;> simp [lineRestriction, lineSubstitution]
  exact RingHom.congr_fun h F

/-- Ambient affine multiplicity at the actual marked point yields root-factor
divisibility of the actual line restriction. For projective multiplicity the
input must first be expressed in a chart; no such bridge is assumed here. -/
theorem lineRestriction_marked_root_power (i v : K) (m : ℕ)
    (F : MvPolynomial (Fin 3) K)
    (hF : AffineMultiplicity.orderAtLeast ![-v, i ^ 2 + i * v, 1] m F) :
    (Polynomial.X + Polynomial.C v) ^ m ∣ lineRestriction i F := by
  have h := AffineMultiplicity.root_power_dvd_of_orderAtLeast
    ![-v, i ^ 2 + i * v, 1] (-v) (lineRestriction i)
    (fun g => by simpa only [mul_neg, sub_neg_eq_add] using lineRestriction_eval i (-v) g)
    m F hF
  simpa only [map_neg, sub_neg_eq_add] using h

end Nagata.W04.ReducibleSquare

end

section

/-!
# Exact additivity of numerical ordinary multiplicity

The polynomial embeds into the genuine formal power-series ring by its actual
coefficients. We identify the finite minimum with that series' order before
using the proved domain multiplicativity theorem. This provides the required
noncancellation bridge, rather than assuming a leading term survives.
-/

namespace Nagata.AffineMultiplicity

variable {σ R : Type*} [CommRing R]

/-- The explicit finite minimum equals the order of the actual polynomial's
coefficientwise embedding in multivariate formal power series. -/
theorem ordinaryMultiplicity_eq_powerSeriesOrder
    (p : σ → R) (f : MvPolynomial σ R) (hf : f ≠ 0) :
    (ordinaryMultiplicity p f hf : ℕ∞) =
      (translateHom p f : MvPowerSeries σ R).order := by
  apply le_antisymm
  · apply MvPowerSeries.nat_le_order
    intro a ha
    exact (orderAtLeast_iff_taylor_coeff p _ f).mp
      (orderAtLeast_ordinaryMultiplicity p f hf) a ha
  · obtain ⟨a, ha, hdegree⟩ := ordinaryMultiplicity_attained p f hf
    have h := MvPowerSeries.order_le
      (f := (translateHom p f : MvPowerSeries σ R)) (d := a) ha
    simpa only [hdegree] using h

/-- Over a coefficient ring without zero divisors, actual ordinary orders add
exactly under multiplication, including products defining reducible curves. -/
theorem ordinaryMultiplicity_mul [NoZeroDivisors R]
    (p : σ → R) (f g : MvPolynomial σ R)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ordinaryMultiplicity p (f * g) (mul_ne_zero hf hg) =
      ordinaryMultiplicity p f hf + ordinaryMultiplicity p g hg := by
  apply ENat.natCast_inj.mp
  rw [ENat.natCast_add, ordinaryMultiplicity_eq_powerSeriesOrder p (f * g) (mul_ne_zero hf hg),
    ordinaryMultiplicity_eq_powerSeriesOrder p f hf,
    ordinaryMultiplicity_eq_powerSeriesOrder p g hg,
    map_mul, MvPolynomial.coe_mul, MvPowerSeries.order_mul]

theorem ordinaryMultiplicity_one [Nontrivial R] (p : σ → R) :
    ordinaryMultiplicity p (1 : MvPolynomial σ R) one_ne_zero = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  have horder := (orderAtLeast_iff_le_ordinaryMultiplicity p 1
    (1 : MvPolynomial σ R) one_ne_zero).mpr h
  have hz := (orderAtLeast_one_iff p (1 : MvPolynomial σ R)).mp horder
  simp at hz

/-- Powers scale numerical multiplicity exactly, including exponent zero and
nonreduced curve equations. Nonvanishing of every power is derived. -/
theorem ordinaryMultiplicity_pow [NoZeroDivisors R] [Nontrivial R]
    (p : σ → R) (f : MvPolynomial σ R) (hf : f ≠ 0) (N : ℕ) :
    ordinaryMultiplicity p (f ^ N) (pow_ne_zero N hf) = ordinaryMultiplicity p f hf * N := by
  induction N with
  | zero => simpa only [pow_zero, Nat.mul_zero] using ordinaryMultiplicity_one p
  | succ N ih =>
      have h := ordinaryMultiplicity_mul p (f ^ N) f (pow_ne_zero N hf) hf
      simpa only [← pow_succ, ih, Nat.mul_succ] using h

end Nagata.AffineMultiplicity

end

section

/-! Exact numerical multiplicity of actual projective products and powers. -/

namespace Nagata.ProjectiveGeometry

/-- Products of actual nonzero homogeneous equations add their numerical
ordinary multiplicities at every projective point. -/
theorem formOrdinaryMultiplicity_mul {d e : ℕ}
    (F : W16.NonzeroHomogeneousForm d) (G : W16.NonzeroHomogeneousForm e)
    (p : PlanePoint) :
    formOrdinaryMultiplicity (F.mul G) p =
      formOrdinaryMultiplicity F p + formOrdinaryMultiplicity G p := by
  obtain ⟨c, hc⟩ := chart_exists p
  rw [formOrdinaryMultiplicity_eq_chart (F.mul G) p c hc,
    formOrdinaryMultiplicity_eq_chart F p c hc,
    formOrdinaryMultiplicity_eq_chart G p c hc]
  have h := AffineMultiplicity.ordinaryMultiplicity_mul (chartCoordinates c p)
    (dehomogenize c F.polynomial) (dehomogenize c G.polynomial)
    (W16.dehomogenize_ne_zero F.homogeneous F.nonzero c)
    (W16.dehomogenize_ne_zero G.homogeneous G.nonzero c)
  simpa only [W16.NonzeroHomogeneousForm.mul, dehomogenize_mul] using h

/-- Repeated factors retain their full numerical multiplicity, including the
zeroth power as the constant equation. -/
theorem formOrdinaryMultiplicity_pow {d : ℕ}
    (F : W16.NonzeroHomogeneousForm d) (N : ℕ) (p : PlanePoint) :
    formOrdinaryMultiplicity (F.pow N) p = formOrdinaryMultiplicity F p * N := by
  obtain ⟨c, hc⟩ := chart_exists p
  rw [formOrdinaryMultiplicity_eq_chart (F.pow N) p c hc,
    formOrdinaryMultiplicity_eq_chart F p c hc]
  have h := AffineMultiplicity.ordinaryMultiplicity_pow (chartCoordinates c p)
    (dehomogenize c F.polynomial)
    (W16.dehomogenize_ne_zero F.homogeneous F.nonzero c) N
  simpa only [W16.NonzeroHomogeneousForm.pow, dehomogenize_pow] using h

/-- The exact product formula also holds after passing to equation classes. -/
theorem classOrdinaryMultiplicity_classOfForm_mul {d e : ℕ}
    (F : W16.NonzeroHomogeneousForm d) (G : W16.NonzeroHomogeneousForm e)
    (p : PlanePoint) :
    classOrdinaryMultiplicity (W16.classOfForm (F.mul G)) p =
      classOrdinaryMultiplicity (W16.classOfForm F) p +
        classOrdinaryMultiplicity (W16.classOfForm G) p := by
  simp only [classOrdinaryMultiplicity_classOfForm, formOrdinaryMultiplicity_mul]

theorem classOrdinaryMultiplicity_classOfForm_pow {d : ℕ}
    (F : W16.NonzeroHomogeneousForm d) (N : ℕ) (p : PlanePoint) :
    classOrdinaryMultiplicity (W16.classOfForm (F.pow N)) p =
      classOrdinaryMultiplicity (W16.classOfForm F) p * N := by
  simp only [classOrdinaryMultiplicity_classOfForm, formOrdinaryMultiplicity_pow]

/-- Arbitrary genuine equation classes may be represented and multiplied,
with exact numerical order independent of the chosen equation representatives. -/
theorem classOrdinaryMultiplicity_representative_product {d e : ℕ}
    (C : W16.PlaneEquationClass d) (D : W16.PlaneEquationClass e) (p : PlanePoint) :
    classOrdinaryMultiplicity
      (W16.classOfForm ((W16.classRepresentative C).mul (W16.classRepresentative D))) p =
      classOrdinaryMultiplicity C p + classOrdinaryMultiplicity D p := by
  rw [classOrdinaryMultiplicity_classOfForm, formOrdinaryMultiplicity_mul]
  rfl

end Nagata.ProjectiveGeometry

end

section

noncomputable section
open scoped BigOperators
namespace Nagata.AffineMultiplicity

theorem ordinaryMultiplicity_finset_prod {σ R ι : Type*} [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] (p : σ → R) (s : Finset ι)
    (f : ι → MvPolynomial σ R) (hf : ∀ i, f i ≠ 0) :
    ordinaryMultiplicity p (∏ i ∈ s, f i)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)) =
      ∑ i ∈ s, ordinaryMultiplicity p (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using ordinaryMultiplicity_one p
  | @insert i s hi ih =>
      have h := ordinaryMultiplicity_mul p (f i) (∏ j ∈ s, f j) (hf i)
        (Finset.prod_ne_zero_iff.mpr (fun j _ => hf j))
      simpa only [Finset.prod_insert hi, Finset.sum_insert hi, ih] using h

theorem ordinaryMultiplicity_finset_prod_pow {σ R ι : Type*} [CommRing R]
    [NoZeroDivisors R] [Nontrivial R] (p : σ → R) (s : Finset ι)
    (f : ι → MvPolynomial σ R) (hf : ∀ i, f i ≠ 0) (n : ι → ℕ) :
    ordinaryMultiplicity p (∏ i ∈ s, f i ^ n i)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hf i))) =
      ∑ i ∈ s, ordinaryMultiplicity p (f i) (hf i) * n i := by
  rw [ordinaryMultiplicity_finset_prod p s _ (fun i => pow_ne_zero _ (hf i))]
  exact Finset.sum_congr rfl (fun i _ => ordinaryMultiplicity_pow p _ (hf i) _)

end Nagata.AffineMultiplicity
namespace Nagata.W15
open Nagata.ProjectiveGeometry

/-- The actual weighted product equation, including zero coefficients and
empty products. Its degree is proved by homogeneity and nonzeroness. -/
def weightedProductForm {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (F : ∀ i, W16.NonzeroHomogeneousForm (d i)) (n : ι → ℕ) :
    W16.NonzeroHomogeneousForm (∑ i ∈ s, d i * n i) where
  polynomial := ∏ i ∈ s, (F i).polynomial ^ n i
  homogeneous := MvPolynomial.IsHomogeneous.prod s _ _ (fun i _ => (F i).homogeneous.pow (n i))
  nonzero := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (F i).nonzero)

theorem weightedProductForm_totalDegree {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (F : ∀ i, W16.NonzeroHomogeneousForm (d i)) (n : ι → ℕ) :
    (weightedProductForm s d F n).polynomial.totalDegree = ∑ i ∈ s, d i * n i :=
  (weightedProductForm s d F n).totalDegree_eq

theorem weightedProductForm_ordinaryMultiplicity {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (F : ∀ i, W16.NonzeroHomogeneousForm (d i)) (n : ι → ℕ) (p : PlanePoint) :
    formOrdinaryMultiplicity (weightedProductForm s d F n) p =
      ∑ i ∈ s, formOrdinaryMultiplicity (F i) p * n i := by
  classical
  obtain ⟨c, hc⟩ := chart_exists p
  simp only [formOrdinaryMultiplicity_eq_chart _ p c hc]
  have heq : dehomogenize c (weightedProductForm s d F n).polynomial =
      ∏ i ∈ s, dehomogenize c (F i).polynomial ^ n i := by
    change (MvPolynomial.eval₂Hom MvPolynomial.C _) (∏ i ∈ s, (F i).polynomial ^ n i) = _
    simp only [map_prod, map_pow]
    rfl
  simpa only [heq] using AffineMultiplicity.ordinaryMultiplicity_finset_prod_pow
    (chartCoordinates c p) s (fun i => dehomogenize c (F i).polynomial)
    (fun i => W16.dehomogenize_ne_zero (F i).homogeneous (F i).nonzero c) n

theorem weightedProductForm_classMultiplicity {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (F : ∀ i, W16.NonzeroHomogeneousForm (d i)) (n : ι → ℕ) (p : PlanePoint) :
    classOrdinaryMultiplicity (W16.classOfForm (weightedProductForm s d F n)) p =
      ∑ i ∈ s, classOrdinaryMultiplicity (W16.classOfForm (F i)) p * n i := by
  simp only [classOrdinaryMultiplicity_classOfForm, weightedProductForm_ordinaryMultiplicity]

/-- Replacing each component equation by another representative of the same
equation class does not change the weighted product's equation class. -/
theorem weightedProductForm_class_independent {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    (F G : ∀ i, W16.NonzeroHomogeneousForm (d i)) (n : ι → ℕ)
    (h : ∀ i, W16.classOfForm (F i) = W16.classOfForm (G i)) :
    W16.classOfForm (weightedProductForm s d F n) =
      W16.classOfForm (weightedProductForm s d G n) := by
  classical
  have hscale := fun i => (W16.classOfForm_eq_iff (F i) (G i)).mp (h i)
  choose a ha using hscale
  apply (W16.classOfForm_eq_iff _ _).mpr
  refine ⟨∏ i ∈ s, a i ^ n i, ?_⟩
  change MvPolynomial.C ((∏ i ∈ s, a i ^ n i : ℂˣ) : ℂ) *
    (∏ i ∈ s, (G i).polynomial ^ n i) = ∏ i ∈ s, (F i).polynomial ^ n i
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val, map_prod, map_pow]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← mul_pow, ha i]

end Nagata.W15

end
end

section

noncomputable section
open scoped BigOperators
namespace Nagata.W15
open Nagata.Workers.W10 Nagata.Workers.W30 Nagata.ProjectiveGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual homogeneous nonzero prime principal ideal of the ternary
coordinate ring. No equation or multiplicity is assumed in this type. -/
def PlanePrimeComponent := {I : Ideal TernaryPolynomial //
  I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal ∧
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)}

def componentCurve (I : PlanePrimeComponent) : EffectivePlaneCurve :=
  ⟨Finsupp.single I.val 1, by
    classical
    constructor
    · exact Finsupp.single_ne_zero.mpr one_ne_zero
    · intro J hJ
      have hJI : J = I.val := by
        simpa only [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] using hJ
      subst J
      exact I.property⟩

def componentDegree (I : PlanePrimeComponent) : ℕ := curveDegree (componentCurve I)
def componentForm (I : PlanePrimeComponent) : W16.NonzeroHomogeneousForm (componentDegree I) :=
  curveForm (componentCurve I)
def componentMultiplicity (I : PlanePrimeComponent) (p : PlanePoint) : ℕ :=
  formOrdinaryMultiplicity (componentForm I) p

theorem componentForm_idealCycle (I : PlanePrimeComponent) :
    equationIdealCycle (componentForm I).polynomial = Finsupp.single I.val 1 :=
  curveEquation_idealCycle (componentCurve I)

theorem equationIdealCycle_finset_prod {ι : Type*} (s : Finset ι)
    (F : ι → TernaryPolynomial) (hF : ∀ i, F i ≠ 0) :
    equationIdealCycle (∏ i ∈ s, F i) = ∑ i ∈ s, equationIdealCycle (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        equationIdealCycle_mul (hF i) (Finset.prod_ne_zero_iff.mpr (fun j _ => hF j)), ih]

def curveComponent (C : EffectivePlaneCurve) (I : C.val.support) : PlanePrimeComponent :=
  ⟨I.val, C.property.2 I.val I.property⟩

def cycleProductForm (C : EffectivePlaneCurve) :=
  weightedProductForm Finset.univ
    (fun I : C.val.support => componentDegree (curveComponent C I))
    (fun I : C.val.support => componentForm (curveComponent C I))
    (fun I : C.val.support => C.val I.val)

theorem cycleProductForm_idealCycle (C : EffectivePlaneCurve) :
    equationIdealCycle (cycleProductForm C).polynomial = C.val := by
  classical
  change equationIdealCycle (∏ I : C.val.support,
    (componentForm (curveComponent C I)).polynomial ^ C.val I.val) = C.val
  rw [equationIdealCycle_finset_prod _ _
    (fun I => pow_ne_zero _ (componentForm (curveComponent C I)).nonzero)]
  have hcomponent (component : C.val.support) :
      equationIdealCycle (componentForm (curveComponent C component)).polynomial =
        Finsupp.single component.val 1 :=
    componentForm_idealCycle (curveComponent C component)
  simp only [equationIdealCycle_pow, hcomponent, Finsupp.smul_single, smul_eq_mul, mul_one]
  change (∑ I : C.val.support, Finsupp.single I.val (C.val I.val)) = C.val
  exact (Finset.sum_coe_sort C.val.support
    (fun I : Ideal TernaryPolynomial => Finsupp.single I (C.val I))).trans
      C.val.sum_single

theorem cycleProductForm_degree (C : EffectivePlaneCurve) :
    (cycleProductForm C).polynomial.totalDegree =
      ∑ I : C.val.support, componentDegree (curveComponent C I) * C.val I.val :=
  weightedProductForm_totalDegree _ _ _ _

theorem cycleProductForm_multiplicity (C : EffectivePlaneCurve) (p : PlanePoint) :
    formOrdinaryMultiplicity (cycleProductForm C) p =
      ∑ I : C.val.support, componentMultiplicity (curveComponent C I) p * C.val I.val :=
  weightedProductForm_ordinaryMultiplicity _ _ _ _ p

end Nagata.W15

end
end

section

noncomputable section
open scoped BigOperators
namespace Nagata.W15
open Nagata.Workers.W10 Nagata.Workers.W30 Nagata.ProjectiveGeometry

/-- Actual ordinary multiplicity of the reconstructed curve equation. -/
def curveOrdinaryMultiplicity (C : EffectivePlaneCurve) (p : PlanePoint) : ℕ :=
  formOrdinaryMultiplicity (curveForm C) p

theorem curveMultiplicityAtLeast_iff_le_ordinaryMultiplicity
    (C : EffectivePlaneCurve) (p : PlanePoint) (m : ℕ) :
    curveMultiplicityAtLeast C p m ↔ m ≤ curveOrdinaryMultiplicity C p :=
  multiplicityAtLeast_iff_le_formOrdinaryMultiplicity (curveForm C) p m

/-- The number agrees with every homogeneous equation realizing the same
full cycle, not merely the same underlying zero set. -/
theorem curveOrdinaryMultiplicity_eq_form (C : EffectivePlaneCurve) {d : ℕ}
    (F : W16.NonzeroHomogeneousForm d) (hcycle : equationIdealCycle F.polynomial = C.val)
    (p : PlanePoint) : curveOrdinaryMultiplicity C p = formOrdinaryMultiplicity F p := by
  apply Nat.le_antisymm
  · apply (multiplicityAtLeast_iff_le_formOrdinaryMultiplicity F p _).mp
    apply (curveMultiplicityAtLeast_iff_equation C F.nonzero hcycle p _).mp
    exact (curveMultiplicityAtLeast_iff_le_ordinaryMultiplicity C p _).mpr le_rfl
  · apply (curveMultiplicityAtLeast_iff_le_ordinaryMultiplicity C p _).mp
    apply (curveMultiplicityAtLeast_iff_equation C F.nonzero hcycle p _).mpr
    exact (multiplicityAtLeast_iff_le_formOrdinaryMultiplicity F p _).mpr le_rfl

theorem curveDegree_eq_component_sum (C : EffectivePlaneCurve) :
    curveDegree C =
      ∑ I : C.val.support, componentDegree (curveComponent C I) * C.val I.val := by
  exact (curveDegree_eq_totalDegree C (cycleProductForm C).nonzero
    (cycleProductForm_idealCycle C)).trans (cycleProductForm_degree C)

theorem curveOrdinaryMultiplicity_eq_component_sum (C : EffectivePlaneCurve) (p : PlanePoint) :
    curveOrdinaryMultiplicity C p =
      ∑ I : C.val.support, componentMultiplicity (curveComponent C I) p * C.val I.val := by
  exact (curveOrdinaryMultiplicity_eq_form C (cycleProductForm C)
    (cycleProductForm_idealCycle C) p).trans (cycleProductForm_multiplicity C p)

theorem componentDegree_eq_formDegree (I : PlanePrimeComponent) {d : ℕ}
    (F : W16.NonzeroHomogeneousForm d)
    (hcycle : equationIdealCycle F.polynomial = Finsupp.single I.val 1) :
    componentDegree I = d :=
  curveDegree_eq_formDegree (componentCurve I) F hcycle

theorem componentMultiplicity_eq_form (I : PlanePrimeComponent) {d : ℕ}
    (F : W16.NonzeroHomogeneousForm d)
    (hcycle : equationIdealCycle F.polynomial = Finsupp.single I.val 1) (p : PlanePoint) :
    componentMultiplicity I p = formOrdinaryMultiplicity F p :=
  curveOrdinaryMultiplicity_eq_form (componentCurve I) F hcycle p

theorem curveOrdinaryMultiplicity_eq_class (C : EffectivePlaneCurve) (p : PlanePoint) :
    curveOrdinaryMultiplicity C p =
      classOrdinaryMultiplicity (curveEquationClass C).equationClass p :=
  (classOrdinaryMultiplicity_classOfForm (curveForm C) p).symm

theorem curveMultiplicityAtLeast_iff_component_sum
    (C : EffectivePlaneCurve) (p : PlanePoint) (m : ℕ) :
    curveMultiplicityAtLeast C p m ↔
      m ≤ ∑ I : C.val.support, componentMultiplicity (curveComponent C I) p * C.val I.val := by
  rw [curveMultiplicityAtLeast_iff_le_ordinaryMultiplicity, curveOrdinaryMultiplicity_eq_component_sum]

end Nagata.W15

end
end

end OAI
