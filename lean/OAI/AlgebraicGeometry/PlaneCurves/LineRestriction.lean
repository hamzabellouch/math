import OAI.AlgebraicGeometry.PlaneCurves.ChartJets
import OAI.AlgebraicGeometry.PlaneCurves.CycleMultiplicity
import OAI.AlgebraicGeometry.PlaneCurves.NormalCharts
import OAI.AlgebraicGeometry.PlaneCurves.NormalCoefficients

namespace OAI

/-!
# Line restriction of homogeneous equations and arrangement products
-/

section

noncomputable section
namespace Nagata.Workers.W24
open Polynomial
open scoped BigOperators

/-- Distinct linear factors divide a polynomial which vanishes at all their
roots, over an arbitrary integral-domain coefficient ring. -/
theorem product_linear_factors_dvd_of_eval_zero {A ι : Type*} [CommRing A] [IsDomain A]
    (a : ι → A) (ha : Function.Injective a) (s : Finset ι) (R : A[X])
    (hzero : ∀ i ∈ s, R.eval (a i) = 0) :
    (∏ i ∈ s, (X - C (a i))) ∣ R := by
  classical
  induction s using Finset.induction_on generalizing R with
  | empty => simp
  | @insert i s hi ih =>
    have hroot : (X - C (a i)) ∣ R :=
      Polynomial.dvd_iff_isRoot.mpr (hzero i (Finset.mem_insert_self i s))
    obtain ⟨T, hRT⟩ := hroot
    have hTzero : ∀ j ∈ s, T.eval (a j) = 0 := by
      intro j hj
      have hz := hzero j (Finset.mem_insert_of_mem hj)
      rw [hRT, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at hz
      have hne : a j - a i ≠ 0 := by
        apply sub_ne_zero.mpr
        intro heq
        exact hi (ha heq ▸ hj)
      exact (mul_eq_zero.mp hz).resolve_left hne
    obtain ⟨Q, hTQ⟩ := ih T hTzero
    refine ⟨Q, ?_⟩
    rw [Finset.prod_insert hi, hRT, hTQ, mul_assoc]

/-- The actual affine graph polynomial of line i, using U=-x. -/
def affineLineGraph (K : Type*) [CommRing K] (i : ℕ) : K[X] :=
  C ((i : K) ^ 2) - C (i : K) * X

/-- Distinct integer line labels give distinct graph polynomials in characteristic zero. -/
theorem affineLineGraph_injective {K : Type*} [CommRing K] [CharZero K] :
    Function.Injective (affineLineGraph K) := by
  intro i j hij
  have hc := congrArg (fun p : K[X] => p.coeff 1) hij
  have hc' : -(i : K) = -(j : K) := by
    simpa only [affineLineGraph, coeff_sub, coeff_C, coeff_C_mul, coeff_X,
      Nat.one_ne_zero, ite_false, ite_true, zero_sub, mul_one] using hc
  exact Nat.cast_injective (neg_injective hc')

/-- Equation of the entire reduced line union in the actual affine plane ring. -/
def lineUnionEquation (K : Type*) [CommRing K] (k : ℕ) : Polynomial (Polynomial K) :=
  ∏ i : Fin k, (X - C (affineLineGraph K i.val))

/-- Actual polynomial restriction to an affine line. -/
def lineRestriction {K : Type*} [CommRing K] (R : Polynomial (Polynomial K))
    (i : ℕ) : Polynomial K := R.eval (affineLineGraph K i)

/-- Divisibility by the reduced line-union equation is exactly vanishing of
all component restrictions, without requiring the global curve to be irreducible. -/
theorem lineUnion_dvd_iff_restrictions_zero {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (R : Polynomial (Polynomial K)) :
    lineUnionEquation K k ∣ R ↔ ∀ i : Fin k, lineRestriction R i.val = 0 := by
  constructor
  · intro h i
    have hfactor : (X - C (affineLineGraph K i.val)) ∣ lineUnionEquation K k :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    exact Polynomial.dvd_iff_isRoot.mp (hfactor.trans h)
  · intro h
    apply product_linear_factors_dvd_of_eval_zero
      (fun i : Fin k => affineLineGraph K i.val)
    · exact affineLineGraph_injective.comp Fin.val_injective
    · intro i _
      exact h i

/-- The algebraic noncancellation bridge needed by reducible normal specialization. -/
theorem exists_nonzero_lineRestriction {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (R : Polynomial (Polynomial K)) (hR : ¬ lineUnionEquation K k ∣ R) :
    ∃ i : Fin k, lineRestriction R i.val ≠ 0 := by
  classical
  have h := mt (lineUnion_dvd_iff_restrictions_zero k R).mpr hR
  simpa only [not_forall] using h

end Nagata.Workers.W24

end
end

section

/-! Domain-level product restriction bridge, applicable before projective
binary dehomogenization by taking A to be a polynomial ring in U and Z. -/
namespace Nagata.Workers.W24
open Polynomial
open scoped BigOperators

/-- A product of distinct monic graph equations divides precisely when every
component evaluation vanishes. -/
theorem linear_product_dvd_iff {A ι : Type*} [CommRing A] [IsDomain A] [Fintype ι]
    (a : ι → A) (ha : Function.Injective a) (R : A[X]) :
    (∏ i, (X - C (a i))) ∣ R ↔ ∀ i, R.eval (a i) = 0 := by
  classical
  constructor
  · intro h i
    exact Polynomial.dvd_iff_isRoot.mp
      ((Finset.dvd_prod_of_mem (fun i => X - C (a i)) (Finset.mem_univ i)).trans h)
  · intro h
    exact product_linear_factors_dvd_of_eval_zero a ha Finset.univ R (fun i _ => h i)

/-- A nonzero residue modulo the line union has a nonzero component restriction. -/
theorem nonzero_component_of_not_linear_product_dvd {A ι : Type*}
    [CommRing A] [IsDomain A] [Fintype ι]
    (a : ι → A) (ha : Function.Injective a) (R : A[X])
    (hR : ¬ (∏ i, (X - C (a i))) ∣ R) :
    ∃ i, R.eval (a i) ≠ 0 := by
  classical
  simpa only [not_forall] using mt (linear_product_dvd_iff a ha R).mpr hR

end Nagata.Workers.W24

end

section

/-!
Homogeneous restriction bridge for the reduced square arrangement, in genuine
ternary coordinates (U,Y,Z). This works before setting Z=1, so no saturation
or unproved projective-section assertion is hidden in noncancellation.
-/
noncomputable section
namespace Nagata.Workers.W24
open scoped BigOperators

private theorem finThreeCases_one {A : Type*} (a : A) (f : Fin 2 → A) :
    Fin.cases a f (1 : Fin 3) = f 0 := rfl

private theorem finThreeCases_two {A : Type*} (a : A) (f : Fin 2 → A) :
    Fin.cases a f (2 : Fin 3) = f 1 := rfl

/-- Binary homogeneous graph Y=i² Z-i U; binary coordinates are U,Z. -/
def homogeneousLineGraph (K : Type*) [CommRing K] (i : ℕ) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C ((i : K) ^ 2) * MvPolynomial.X 1 -
    MvPolynomial.C (i : K) * MvPolynomial.X 0

/-- The actual homogeneous linear equation Y-i²Z+iU. -/
def homogeneousLineEquation (K : Type*) [CommRing K] (i : ℕ) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 1 - (MvPolynomial.C ((i : K) ^ 2) * MvPolynomial.X 2 -
    MvPolynomial.C (i : K) * MvPolynomial.X 0)

/-- Regard the actual ternary ring as polynomials in Y with binary U,Z coefficients. -/
def ternaryAsPolynomialInY (K : Type*) [CommSemiring K] :
    MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 3) 1)).trans
    (MvPolynomial.finSuccEquiv K 2)

/-- Binary restrictions are ordinary ring evaluations in the Y variable. -/
def homogeneousLineRestriction {K : Type*} [CommRing K]
    (R : MvPolynomial (Fin 3) K) (i : ℕ) : MvPolynomial (Fin 2) K :=
  (ternaryAsPolynomialInY K R).eval (homogeneousLineGraph K i)

/-- Explicit homogeneous coordinate substitution (U,Y,Z)=(U,i²Z-iU,Z). -/
def homogeneousLineSubstitution (K : Type*) [CommRing K] (i : ℕ) :
    Fin 3 → MvPolynomial (Fin 2) K :=
  ![MvPolynomial.X 0, homogeneousLineGraph K i, MvPolynomial.X 1]

/-- Homogeneous equation of the reduced union of k lines. -/
def homogeneousLineUnion (K : Type*) [CommRing K] (k : ℕ) : MvPolynomial (Fin 3) K :=
  ∏ i : Fin k, homogeneousLineEquation K i.val

theorem homogeneousLineGraph_homogeneous {K : Type*} [CommRing K] (i : ℕ) :
    (homogeneousLineGraph K i).IsHomogeneous 1 := by
  exact ((MvPolynomial.isHomogeneous_X K 1).C_mul ((i : K) ^ 2)).sub
    ((MvPolynomial.isHomogeneous_X K 0).C_mul (i : K))

/-- The polynomial-ring restriction agrees with the actual homogeneous coordinate map. -/
theorem homogeneousLineRestriction_eq_eval₂ {K : Type*} [CommRing K]
    (R : MvPolynomial (Fin 3) K) (i : ℕ) :
    homogeneousLineRestriction R i = MvPolynomial.eval₂ MvPolynomial.C
      (homogeneousLineSubstitution K i) R := by
  have h : (Polynomial.evalRingHom (homogeneousLineGraph K i)).comp
      (ternaryAsPolynomialInY K).toRingHom =
      MvPolynomial.eval₂Hom MvPolynomial.C (homogeneousLineSubstitution K i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ternaryAsPolynomialInY, MvPolynomial.renameEquiv_apply,
        MvPolynomial.finSuccEquiv_apply]
    · intro j
      fin_cases j <;>
        simp [ternaryAsPolynomialInY, homogeneousLineSubstitution,
          MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply,
          Equiv.swap_apply_def, finThreeCases_one, finThreeCases_two]
  exact congrArg (fun f : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K => f R) h

/-- Restricting a homogeneous form to any component preserves its homogeneous degree. -/
theorem homogeneousLineRestriction_homogeneous {K : Type*} [CommRing K]
    (R : MvPolynomial (Fin 3) K) (i d : ℕ) (hR : R.IsHomogeneous d) :
    (homogeneousLineRestriction R i).IsHomogeneous d := by
  rw [homogeneousLineRestriction_eq_eval₂]
  have hcoords : ∀ j, (homogeneousLineSubstitution K i j).IsHomogeneous 1 := by
    intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X K 0
    · exact homogeneousLineGraph_homogeneous i
    · exact MvPolynomial.isHomogeneous_X K 1
  simpa only [one_mul] using hR.eval₂ MvPolynomial.C
    (homogeneousLineSubstitution K i) (fun r => MvPolynomial.isHomogeneous_C (Fin 2) r) hcoords

theorem homogeneousLineEquation_homogeneous {K : Type*} [CommRing K] (i : ℕ) :
    (homogeneousLineEquation K i).IsHomogeneous 1 := by
  exact (MvPolynomial.isHomogeneous_X K 1).sub
    (((MvPolynomial.isHomogeneous_X K 2).C_mul ((i : K) ^ 2)).sub
      ((MvPolynomial.isHomogeneous_X K 0).C_mul (i : K)))

theorem homogeneousLineUnion_homogeneous {K : Type*} [CommRing K] (k : ℕ) :
    (homogeneousLineUnion K k).IsHomogeneous k := by
  simpa only [homogeneousLineUnion, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
    using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin k => homogeneousLineEquation K i.val) (fun _ => 1)
      (fun i _ => homogeneousLineEquation_homogeneous i.val)

theorem homogeneousLineGraph_injective {K : Type*} [CommRing K] [CharZero K] :
    Function.Injective (homogeneousLineGraph K) := by
  intro i j h
  have he := congrArg (MvPolynomial.eval (fun v : Fin 2 => if v = 0 then (1 : K) else 0)) h
  simpa [homogeneousLineGraph] using he

/-- The actual line equation maps to the monic factor used by product restriction. -/
theorem ternaryAsPolynomialInY_line {K : Type*} [CommRing K] (i : ℕ) :
    ternaryAsPolynomialInY K (homogeneousLineEquation K i) =
      Polynomial.X - Polynomial.C (homogeneousLineGraph K i) := by
  simp [ternaryAsPolynomialInY, homogeneousLineEquation, homogeneousLineGraph,
    MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply,
    Equiv.swap_apply_def, finThreeCases_one, finThreeCases_two]

theorem ternaryAsPolynomialInY_union {K : Type*} [CommRing K] (k : ℕ) :
    ternaryAsPolynomialInY K (homogeneousLineUnion K k) =
      ∏ i : Fin k, (Polynomial.X - Polynomial.C (homogeneousLineGraph K i.val)) := by
  simp only [homogeneousLineUnion, map_prod, ternaryAsPolynomialInY_line]

/-- Genuine global component noncancellation, before affine dehomogenization. -/
theorem homogeneousUnion_dvd_iff_restrictions_zero {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (R : MvPolynomial (Fin 3) K) :
    homogeneousLineUnion K k ∣ R ↔ ∀ i : Fin k, homogeneousLineRestriction R i.val = 0 := by
  rw [← map_dvd_iff (ternaryAsPolynomialInY K), ternaryAsPolynomialInY_union]
  exact linear_product_dvd_iff (fun i : Fin k => homogeneousLineGraph K i.val)
    (homogeneousLineGraph_injective.comp Fin.val_injective) (ternaryAsPolynomialInY K R)

theorem exists_nonzero_homogeneousLineRestriction {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (R : MvPolynomial (Fin 3) K) (hR : ¬ homogeneousLineUnion K k ∣ R) :
    ∃ i : Fin k, homogeneousLineRestriction R i.val ≠ 0 := by
  classical
  simpa only [not_forall] using mt (homogeneousUnion_dvd_iff_restrictions_zero k R).mpr hR

end Nagata.Workers.W24

end
end

section

/-! Connect global homogeneous restriction to the actual affine component map
used by the checked cycle obstruction. All coordinates are (U,Y,Z). -/
noncomputable section
namespace Nagata.Workers.W24

/-- Dehomogenizing the genuine binary component restriction is exactly the
literal substitution (U,Y,Z)=(U,i²-iU,1). -/
theorem binaryAffine_homogeneousLineRestriction
    (R : MvPolynomial (Fin 3) ℂ) (i : ℕ) :
    Nagata.W16.binaryAffine (homogeneousLineRestriction R i) =
      Nagata.W04.ReducibleSquare.lineRestriction (i : ℂ) R := by
  rw [homogeneousLineRestriction_eq_eval₂]
  let f : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = 0 then Polynomial.X else 1)
  change f (MvPolynomial.eval₂Hom MvPolynomial.C (homogeneousLineSubstitution ℂ i) R) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hC : f.comp MvPolynomial.C = Polynomial.C := by
    ext c
    simp [f]
  have hcoords : (fun j => f (homogeneousLineSubstitution ℂ i j)) =
      Nagata.W04.ReducibleSquare.lineSubstitution (i : ℂ) := by
    funext j
    fin_cases j <;>
      simp [f, homogeneousLineSubstitution, homogeneousLineGraph,
        Nagata.W04.ReducibleSquare.lineSubstitution]
  rw [hC, hcoords]
  rfl

/-- Vanishing of one actual affine component restriction is equivalent to
vanishing of its binary homogeneous restriction for a fixed-degree form. -/
theorem affine_lineRestriction_eq_zero_iff
    (R : MvPolynomial (Fin 3) ℂ) (i d : ℕ) (hR : R.IsHomogeneous d) :
    Nagata.W04.ReducibleSquare.lineRestriction (i : ℂ) R = 0 ↔
      homogeneousLineRestriction R i = 0 := by
  rw [← binaryAffine_homogeneousLineRestriction]
  constructor
  · exact Nagata.W16.binaryAffine_eq_zero_imp
      (homogeneousLineRestriction_homogeneous R i d hR)
  · intro hz
    rw [hz]
    simp [Nagata.W16.binaryAffine]

/-- Nonzero residue modulo the homogeneous union supplies a nonzero actual
affine line restriction. Fixed-degree dehomogenization supplies the needed
bridge rather than an unproved saturation assertion. -/
theorem exists_nonzero_affine_lineRestriction
    (k d : ℕ) (R : MvPolynomial (Fin 3) ℂ) (hR : R.IsHomogeneous d)
    (hnotdvd : ¬ homogeneousLineUnion ℂ k ∣ R) :
    ∃ i : Fin k, Nagata.W04.ReducibleSquare.lineRestriction (i.val : ℂ) R ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_nonzero_homogeneousLineRestriction k R hnotdvd
  refine ⟨i, ?_⟩
  rw [← binaryAffine_homogeneousLineRestriction]
  exact Nagata.W16.binaryAffine_ne_zero
    (homogeneousLineRestriction_homogeneous R i.val d hR) hi

end Nagata.Workers.W24

end
end

section

/-! Actual equation compatibility between homogeneous, affine, and nested rings. -/
namespace Nagata.Workers.W24

theorem bivariateToNested_directChart_line (i : ℕ) :
    Nagata.W18.bivariateToNested (Nagata.W27.directChartHom 2 (homogeneousLineEquation ℂ i)) =
      Polynomial.X - Polynomial.C (affineLineGraph ℂ i) := by
  simp [Nagata.W27.directChartHom, homogeneousLineEquation,
    Fin.insertNth_apply_below (show (0 : Fin 3) < 2 from by decide),
    Fin.insertNth_apply_below (show (1 : Fin 3) < 2 from by decide),
    Nagata.W18.bivariateToNested, affineLineGraph]

theorem bivariateToNested_directChart_union (k : ℕ) :
    Nagata.W18.bivariateToNested (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k)) =
      lineUnionEquation ℂ k := by
  simp only [homogeneousLineUnion, map_prod, bivariateToNested_directChart_line,
    lineUnionEquation]

theorem directChart_union_eq_nestedToBivariate (k : ℕ) :
    Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k) =
      Nagata.W18.nestedToBivariate (lineUnionEquation ℂ k) := by
  have h := congrArg (Nagata.W18.nestedToBivariate (K := ℂ))
    (bivariateToNested_directChart_union k)
  have hinv := RingHom.congr_fun
    (Nagata.W18.nestedToBivariate_comp_bivariateToNested (K := ℂ))
    (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k))
  simp only [RingHom.comp_apply, RingHom.id_apply] at hinv
  change Nagata.W18.nestedToBivariate
    (Nagata.W18.bivariateToNested (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k))) = _ at h
  rw [hinv] at h
  exact h

end Nagata.Workers.W24

end

section

/-! Exact coordinate compatibility needed by the local analytic normal chart. -/
namespace Nagata.Workers.W24
open MvPolynomial

/-- Evaluation of the actual Z=1 dehomogenization is normalized ternary evaluation. -/
theorem planePolynomialEval_directChart (R : MvPolynomial (Fin 3) ℂ) (u y : ℂ) :
    Nagata.Workers.W28.planePolynomialEval (Nagata.W27.directChartHom 2 R) (u, y) =
      MvPolynomial.eval ![u, y, 1] R := by
  have h : (MvPolynomial.eval (fun j : Fin 2 => if j = 0 then u else y)).comp
      (Nagata.W27.directChartHom 2) = MvPolynomial.eval ![u, y, 1] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Nagata.W27.directChartHom]
    · intro j
      fin_cases j <;>
        simp [Nagata.W27.directChartHom,
          Fin.insertNth_apply_below (show (0 : Fin 3) < 2 from by decide),
          Fin.insertNth_apply_below (show (1 : Fin 3) < 2 from by decide)]
  exact RingHom.congr_fun h R

/-- The analytic-chart plane polynomial on the selected graph is the exact
univariate line restriction used in the square obstruction. -/
theorem planePolynomialEval_directChart_on_line
    (R : MvPolynomial (Fin 3) ℂ) (i u : ℂ) :
    Nagata.Workers.W28.planePolynomialEval (Nagata.W27.directChartHom 2 R)
      (u, i ^ 2 - i * u) =
        (Nagata.W04.ReducibleSquare.lineRestriction i R).eval u := by
  rw [planePolynomialEval_directChart, Nagata.W04.ReducibleSquare.lineRestriction_eval]

end Nagata.Workers.W24

end

end OAI
