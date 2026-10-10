import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialBridge
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.SelectedLengthContradiction

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace WeightedTorusJets.W25

open MvPolynomial
open Result.Workers.W57

variable (K : Type*) [Field K]

def seriesConstant : K →+* Series₃ K :=
  PowerSeries.C.comp (PowerSeries.C.comp PowerSeries.C)

def polynomialSeries : MvPolynomial (Fin 3) K →+* Series₃ K :=
  MvPolynomial.eval₂Hom (seriesConstant K) (coordinate K)

theorem polynomialSeries_monomial (m : Fin 3 →₀ ℕ) (r : K) :
    polynomialSeries K (MvPolynomial.monomial m r) =
      PowerSeries.monomial (m 0)
        (PowerSeries.monomial (m 1) (PowerSeries.monomial (m 2) r)) := by
  classical
  rw [polynomialSeries, MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
  simp only [seriesConstant, RingHom.comp_apply, coordinate,
    PowerSeries.monomial_eq_C_mul_X_pow, map_mul, map_pow]
  ac_rfl

theorem coeff_polynomialSeries (p : MvPolynomial (Fin 3) K) (m : Fin 3 →₀ ℕ) :
    PowerSeries.coeff (m 2) (PowerSeries.coeff (m 1)
      (PowerSeries.coeff (m 0) (polynomialSeries K p))) = p.coeff m := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  have heq (d : Fin 3 →₀ ℕ) :
      (m 0 = d 0 ∧ m 1 = d 1 ∧ m 2 = d 2) ↔ m = d := by
    constructor
    · rintro ⟨h0, h1, h2⟩
      ext i
      fin_cases i <;> assumption
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩
  simp only [map_sum, polynomialSeries_monomial, PowerSeries.coeff_monomial,
    apply_ite, map_zero, ← ite_and, and_assoc, heq]
  by_cases hm : m ∈ p.support
  · simp [hm]
  · simp [hm, MvPolynomial.notMem_support_iff.mp hm]

def exponent₃ (i j k : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![i, j, k]

@[simp] theorem exponent₃_zero (i j k : ℕ) : exponent₃ i j k 0 = i := rfl
@[simp] theorem exponent₃_one (i j k : ℕ) : exponent₃ i j k 1 = j := rfl
@[simp] theorem exponent₃_two (i j k : ℕ) : exponent₃ i j k 2 = k := rfl

theorem rectangleProjection_surjective (a b c : ℕ) :
    Function.Surjective (rectangleProjection K a b c) := by
  apply Function.Surjective.comp
    (Ideal.Quotient.mk_surjective :
      Function.Surjective (jetProjection (Jet (Jet K c) b) a))
  apply Function.Surjective.comp
    (PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective)
  exact PowerSeries.map_surjective _
    (PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective)

def polynomialRectangleMap (t : Fin 3 → ℕ) :
    MvPolynomial (Fin 3) K →+* RectangleJet K (t 0 + 1) (t 1 + 1) (t 2 + 1) :=
  (rectangleProjection K (t 0 + 1) (t 1 + 1) (t 2 + 1)).comp (polynomialSeries K)

theorem polynomialRectangleMap_eq_zero_iff (t : Fin 3 → ℕ)
    (p : MvPolynomial (Fin 3) K) :
    polynomialRectangleMap K t p = 0 ↔ boxCoefficients t p = 0 := by
  classical
  change rectangleProjection K _ _ _ (polynomialSeries K p) = 0 ↔ _
  rw [rectangleProjection_eq_zero_iff]
  constructor
  · intro hp
    funext a
    change p.coeff (boxExponent t a) = 0
    rw [← coeff_polynomialSeries]
    exact hp _ (a 0).isLt _ (a 1).isLt _ (a 2).isLt
  · intro hp i hi j hj k hk
    let m := exponent₃ i j k
    have hm : ∀ v, m v < t v + 1 := by
      intro v
      fin_cases v <;> assumption
    let a : Box t := fun v => ⟨m v, hm v⟩
    have ha : boxExponent t a = m := by ext v; rfl
    have hz := congrFun hp a
    have hz' : p.coeff m = 0 := by
      simpa only [boxCoefficients_apply, ha, Pi.zero_apply] using hz
    simpa only [m, exponent₃_zero, exponent₃_one, exponent₃_two]
      using (coeff_polynomialSeries K p m).trans hz'

theorem polynomialRectangleMap_ker (t : Fin 3 → ℕ) :
    RingHom.ker (polynomialRectangleMap K t) = truncationIdeal (K := K) t := by
  ext p
  change polynomialRectangleMap K t p = 0 ↔ p ∈ truncationIdeal (K := K) t
  rw [polynomialRectangleMap_eq_zero_iff]
  change p ∈ LinearMap.ker (boxCoefficients t) ↔ _
  rw [ker_boxCoefficients]
  rfl

theorem polynomialRectangleMap_surjective (t : Fin 3 → ℕ) :
    Function.Surjective (polynomialRectangleMap K t) := by
  classical
  intro y
  obtain ⟨f, rfl⟩ := rectangleProjection_surjective K (t 0 + 1) (t 1 + 1) (t 2 + 1) y
  obtain ⟨p, hp⟩ := boxCoefficients_surjective (K := K) t
    (fun a => PowerSeries.coeff (a 2).val (PowerSeries.coeff (a 1).val
      (PowerSeries.coeff (a 0).val f)))
  refine ⟨p, ?_⟩
  change rectangleProjection K _ _ _ (polynomialSeries K p) = rectangleProjection K _ _ _ f
  rw [← sub_eq_zero, ← map_sub, rectangleProjection_eq_zero_iff]
  intro i hi j hj k hk
  let m := exponent₃ i j k
  have hm : ∀ v, m v < t v + 1 := by
    intro v
    fin_cases v <;> assumption
  let a : Box t := fun v => ⟨m v, hm v⟩
  have ha : boxExponent t a = m := by ext v; rfl
  have hcoeff := congrFun hp a
  have hcoeff' : p.coeff m = PowerSeries.coeff k
      (PowerSeries.coeff j (PowerSeries.coeff i f)) := by
    simpa only [boxCoefficients_apply, ha, a, m,
      exponent₃_zero, exponent₃_one, exponent₃_two] using hcoeff
  simp only [map_sub]
  rw [show PowerSeries.coeff k (PowerSeries.coeff j
    (PowerSeries.coeff i (polynomialSeries K p))) = p.coeff m from
    coeff_polynomialSeries K p m, hcoeff', sub_self]

def polynomialRectangleEquiv (t : Fin 3 → ℕ) :
    (MvPolynomial (Fin 3) K ⧸ truncationIdeal (K := K) t) ≃+*
      RectangleJet K (t 0 + 1) (t 1 + 1) (t 2 + 1) :=
  (Ideal.quotEquivOfEq (polynomialRectangleMap_ker K t).symm).trans
    ((polynomialRectangleMap K t).quotientKerEquivOfSurjective
      (polynomialRectangleMap_surjective K t))

end WeightedTorusJets.W25

end

end

end SiegelZeros

end OAI
