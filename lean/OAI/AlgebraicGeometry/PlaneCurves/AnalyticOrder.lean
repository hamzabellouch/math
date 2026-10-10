import OAI.AlgebraicGeometry.PlaneCurves.AnalyticTaylor
import OAI.AlgebraicGeometry.PlaneCurves.CoefficientSpaces
import OAI.AlgebraicGeometry.PlaneCurves.FrechetMultiplicity
import OAI.AlgebraicGeometry.PlaneCurves.MixedDerivatives
import OAI.AlgebraicGeometry.PlaneCurves.NormalCoefficients

namespace OAI

/-!
# Analytic coefficient order, nested order, and ideal-power multiplicity
-/

section

noncomputable section
namespace Nagata.W18
open Nagata.CoefficientSpaces

/-- Exact transverse derivative of an actual polynomial of function coefficients.
No analyticity assumption on the coefficient functions is needed for this identity. -/
theorem scalarExpression_iteratedDeriv_zero
    (F : Polynomial (ℂ → ℂ)) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (fun w => scalarExpression F z w) 0 =
      (j.factorial : ℂ) * F.coeff j z := by
  classical
  simp only [scalarExpression, Polynomial.sum_def]
  rw [iteratedDeriv_fun_sum (fun k _ =>
    contDiffAt_const.mul (contDiffAt_id.pow k))]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro k hk hkj
    simp [Ne.symm hkj]
  · intro hj
    have hc : F.coeff j = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using hj
    simp [hc]

/-- Nonzero constant multiplication preserves analytic order of an analytic germ. -/
theorem analyticOrderAt_nonzero_const_mul
    (f : ℂ → ℂ) (a c : ℂ) (hc : c ≠ 0) (hf : AnalyticAt ℂ f a) :
    analyticOrderAt (fun z => c * f z) a = analyticOrderAt f a := by
  have hconst : AnalyticAt ℂ (fun _ : ℂ => c) a := analyticAt_const
  change analyticOrderAt ((fun _ : ℂ => c) * f) a = _
  rw [analyticOrderAt_mul hconst hf, hconst.analyticOrderAt_eq_zero.mpr hc, zero_add]

/-- Joint analyticity forces analyticity of every actual function coefficient,
including indices above the polynomial degree. -/
theorem scalar_coefficient_analyticAt
    (F : Polynomial (ℂ → ℂ)) (a : ℂ) (j : ℕ)
    (hF : AnalyticAt ℂ (fun p : ℂ × ℂ => scalarExpression F p.1 p.2) (a, 0)) :
    AnalyticAt ℂ (F.coeff j) a := by
  have hd := Nagata.W19.analyticAt_transverse_iteratedDeriv a hF j
  have he : (fun x => iteratedDeriv j (fun y => scalarExpression F x y) 0) =
      (fun x => (j.factorial : ℂ) * F.coeff j x) := by
    funext x
    exact scalarExpression_iteratedDeriv_zero F j x
  rw [he] at hd
  have hc : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hh := (analyticAt_const (v := (j.factorial : ℂ)⁻¹)).mul hd
  change AnalyticAt ℂ (fun x => (j.factorial : ℂ)⁻¹ *
    ((j.factorial : ℂ) * F.coeff j x)) a at hh
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hh

/-- Ordinary analytic order at a zero-displacement point gives order `m-j`
of every genuine scalar coefficient, with natural truncated subtraction. -/
theorem scalar_coefficient_order
    (F : Polynomial (ℂ → ℂ)) (a : ℂ) (m j : ℕ)
    (hF : Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun p : ℂ × ℂ => scalarExpression F p.1 p.2) (a, 0) m) :
    ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) a := by
  obtain ⟨P, hP, hzero⟩ := hF
  have ho := Nagata.W19.transverse_iteratedDeriv_order_of_powerSeries a hP m j hzero
  have he : (fun x => iteratedDeriv j (fun y => scalarExpression F x y) 0) =
      (fun x => (j.factorial : ℂ) * F.coeff j x) := by
    funext x
    exact scalarExpression_iteratedDeriv_zero F j x
  rw [he] at ho
  rw [analyticOrderAt_nonzero_const_mul (F.coeff j) a (j.factorial : ℂ)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))
    (scalar_coefficient_analyticAt F a j ⟨P, hP⟩)] at ho
  exact ho

end Nagata.W18

end
end

section

/-!
# Actual analytic Taylor order implies ordinary polynomial multiplicity
-/

noncomputable section
namespace Nagata.W18

open Nagata.Workers.W30
open Nagata.AffineMultiplicity
open Nagata.Workers.W28

/-- Centered convergent-series vanishing forces every low polynomial coefficient
zero. The nonzero factorials are cancelled in the actual field ℂ. -/
theorem polynomial_coeff_zero_of_centered_powerSeries
    (P : MvPolynomial (Fin 2) ℂ)
    (S : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (hS : HasFPowerSeriesAt (fun z : ℂ × ℂ => planeValue P z.1 z.2) S 0)
    (m : ℕ) (hzero : ∀ n < m, S n = 0) :
    ∀ ell b : ℕ, ell + b < m → P.coeff (exponentPair ell b) = 0 := by
  intro ell b hlt
  have hd := Nagata.W19.mixed_iteratedDeriv_zero_of_powerSeries 0 hS m hzero ell b hlt
  change mixedDerivative ell b P 0 0 = 0 at hd
  rw [mixedDerivative_zero] at hd
  have hfac : (ell.factorial : ℂ) * (b.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero ell))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b))
  exact (mul_eq_zero.mp hd).resolve_left hfac

/-- A convergent series at any actual affine point with low terms zero forces
membership in the corresponding point-ideal power. -/
theorem polynomial_ideal_order_of_powerSeries
    (P : MvPolynomial (Fin 2) ℂ) (p : ℂ × ℂ)
    (S : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (hS : HasFPowerSeriesAt (fun z : ℂ × ℂ => planeValue P z.1 z.2) S p)
    (m : ℕ) (hzero : ∀ n < m, S n = 0) :
    orderAtLeast (planePoint p.1 p.2) m P := by
  have hshift := hS.comp_sub (-p)
  simp only [add_neg_cancel] at hshift
  have htranslated : HasFPowerSeriesAt
      (fun z : ℂ × ℂ => planeValue (translateHom (planePoint p.1 p.2) P) z.1 z.2)
      S 0 := by
    apply hshift.congr
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [planeValue_translate]
      simp only [sub_neg_eq_add, Prod.fst_add, Prod.snd_add]
  apply (orderAtLeast_finTwo_iff_taylor_coeff (planePoint p.1 p.2) m P).mpr
  exact polynomial_coeff_zero_of_centered_powerSeries _ S htranslated m hzero

theorem planePoint_eq_coordinate_function (p : ℂ × ℂ) :
    planePoint p.1 p.2 = (fun i : Fin 2 => if i = 0 then p.1 else p.2) := by
  funext i
  fin_cases i <;> rfl

theorem polynomial_analytic_order_implies_ideal_order
    (P : MvPolynomial (Fin 2) ℂ) (p : ℂ × ℂ) (m : ℕ)
    (hP : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => MvPolynomial.eval
        (fun i => if i = 0 then z.1 else z.2) P) p m) :
    orderAtLeast (fun i : Fin 2 => if i = 0 then p.1 else p.2) m P := by
  obtain ⟨S, hS, hzero⟩ := hP
  have hseries : HasFPowerSeriesAt (fun z : ℂ × ℂ => planeValue P z.1 z.2) S p := by
    simpa only [planeValue, planePoint_eq_coordinate_function] using hS
  have h := polynomial_ideal_order_of_powerSeries P p S hseries m hzero
  rwa [planePoint_eq_coordinate_function] at h

/-- Ordinary ideal-power multiplicity and existence of a genuine convergent
Taylor expansion with low terms zero are equivalent for actual plane polynomials. -/
theorem polynomial_analytic_order_iff_ideal_order
    (P : MvPolynomial (Fin 2) ℂ) (p : ℂ × ℂ) (m : ℕ) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => MvPolynomial.eval
        (fun i => if i = 0 then z.1 else z.2) P) p m ↔
    orderAtLeast (fun i : Fin 2 => if i = 0 then p.1 else p.2) m P :=
  ⟨polynomial_analytic_order_implies_ideal_order P p m,
    polynomial_order_implies_analytic_order P p m⟩

/-- The analytic normal-limit order can now be passed to the actual nested
polynomial point ideal used by the coefficient and fiber-order package. -/
theorem nested_ideal_order_of_analytic_order
    (P : MvPolynomial (Fin 2) ℂ) (a c : ℂ) (m : ℕ)
    (hP : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => MvPolynomial.eval
        (fun i => if i = 0 then z.1 else z.2) P) (a, c) m) :
    bivariateToNested P ∈ (nestedPointIdeal a c) ^ m := by
  apply nested_order_of_affine_order a c m P
  have h := polynomial_analytic_order_implies_ideal_order P (a, c) m hP
  convert h using 1
  funext i
  fin_cases i <;> rfl

/-- Analytic order directly forces base order of the highest possible fiber
coefficient of the actual local polynomial. -/
theorem analytic_top_coefficient_base_divisibility
    (P : MvPolynomial (Fin 2) ℂ) (a c : ℂ) (m J : ℕ)
    (hP : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => MvPolynomial.eval
        (fun i => if i = 0 then z.1 else z.2) P) (a, c) m)
    (hJ : (bivariateToNested P).natDegree ≤ J) :
    (Polynomial.X - Polynomial.C a) ^ (m - J) ∣ (bivariateToNested P).coeff J :=
  top_coefficient_base_divisibility _ a c m J hJ
    (nested_ideal_order_of_analytic_order P a c m hP)

/-- Analytic order directly gives the actual marked fiber root divisibility. -/
theorem analytic_fiber_power_divides
    (P : MvPolynomial (Fin 2) ℂ) (a c : ℂ) (m : ℕ)
    (hP : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => MvPolynomial.eval
        (fun i => if i = 0 then z.1 else z.2) P) (a, c) m) :
    (Polynomial.X - Polynomial.C c) ^ m ∣ fiberRestriction a (bivariateToNested P) :=
  fiber_power_divides_of_surface_order _ a c m
    (nested_ideal_order_of_analytic_order P a c m hP)

end Nagata.W18

end
end

section

/-! Direct analytic-to-ideal interface for the actual nested normal polynomial.
Evaluation below is ordinary polynomial evaluation in W followed by U. -/

noncomputable section
namespace Nagata.W18
open Nagata.Workers.W28

/-- Explicit inverse-coordinate evaluation identity. -/
theorem nestedEvaluation_eq_polynomialEvaluation
    (H : Polynomial (Polynomial ℂ)) (z : ℂ × ℂ) :
    (H.eval (Polynomial.C z.2)).eval z.1 =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
        (nestedToBivariate H) := by
  have h := eval_bivariateToNested z.1 z.2 (nestedToBivariate H)
  have hinv : bivariateToNested (nestedToBivariate H) = H :=
    RingHom.congr_fun bivariateToNested_comp_nestedToBivariate H
  rw [hinv] at h
  have hcoords : ![z.1, z.2] = (fun i : Fin 2 => if i = 0 then z.1 else z.2) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hcoords] using h

/-- A genuine convergent analytic-order statement for H(U,W) implies its
actual nested point-ideal-power membership. -/
theorem nested_polynomial_ideal_order_of_analytic_order
    (H : Polynomial (Polynomial ℂ)) (a c : ℂ) (m : ℕ)
    (hH : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => (H.eval (Polynomial.C z.2)).eval z.1) (a, c) m) :
    H ∈ (nestedPointIdeal a c) ^ m := by
  have hP : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => MvPolynomial.eval
        (fun i => if i = 0 then z.1 else z.2) (nestedToBivariate H)) (a, c) m := by
    simpa only [nestedEvaluation_eq_polynomialEvaluation] using hH
  have h := nested_ideal_order_of_analytic_order (nestedToBivariate H) a c m hP
  have hinv : bivariateToNested (nestedToBivariate H) = H :=
    RingHom.congr_fun bivariateToNested_comp_nestedToBivariate H
  rwa [hinv] at h

/-- Direct genuine-series version of the nested polynomial order bridge. -/
theorem nested_polynomial_ideal_order_of_powerSeries
    (H : Polynomial (Polynomial ℂ)) (a c : ℂ)
    (S : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (hS : HasFPowerSeriesAt
      (fun z : ℂ × ℂ => (H.eval (Polynomial.C z.2)).eval z.1) S (a, c))
    (m : ℕ) (hzero : ∀ n < m, S n = 0) :
    H ∈ (nestedPointIdeal a c) ^ m :=
  nested_polynomial_ideal_order_of_analytic_order H a c m ⟨S, hS, hzero⟩

/-- The analytic limit's actual local polynomial top coefficient has the
required base vanishing divisibility. -/
theorem nested_analytic_top_coefficient_divisibility
    (H : Polynomial (Polynomial ℂ)) (a c : ℂ) (m J : ℕ)
    (hH : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => (H.eval (Polynomial.C z.2)).eval z.1) (a, c) m)
    (hJ : H.natDegree ≤ J) :
    (Polynomial.X - Polynomial.C a) ^ (m - J) ∣ H.coeff J :=
  top_coefficient_base_divisibility H a c m J hJ
    (nested_polynomial_ideal_order_of_analytic_order H a c m hH)

/-- The analytic limit's actual local polynomial has the required fiber root. -/
theorem nested_analytic_fiber_divisibility
    (H : Polynomial (Polynomial ℂ)) (a c : ℂ) (m : ℕ)
    (hH : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun z : ℂ × ℂ => (H.eval (Polynomial.C z.2)).eval z.1) (a, c) m) :
    (Polynomial.X - Polynomial.C c) ^ m ∣ fiberRestriction a H :=
  fiber_power_divides_of_surface_order H a c m
    (nested_polynomial_ideal_order_of_analytic_order H a c m hH)

end Nagata.W18

end
end

end OAI
