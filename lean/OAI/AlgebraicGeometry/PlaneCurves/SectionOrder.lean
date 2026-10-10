import OAI.AlgebraicGeometry.PlaneCurves.NormalPolynomials
import OAI.AlgebraicGeometry.PlaneCurves.ThetaLimits

namespace OAI

/-!
# Local, orbit, and marked order of normal polynomial sections
-/

section

namespace Nagata.CoefficientSpaces
open Nagata.Workers.W28

/-- Actual covering lifts of the moving logarithmic centers, on fibre value one. -/
noncomputable def logarithmicPoints {q : ℕ} (z₀ : ℂ) (ξ : Fin q → ℂ) : Fin q → ℂ × ℂ :=
  fun i => (z₀ * Complex.exp (ξ i), 1)

/-- The actual exponential coordinate expression inherits genuine Taylor order
by analytic substitution in both base and fibre coordinates. -/
theorem localScalar_order_of_cover_order {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (F : Nagata.W20.ActualSection τ γL γP d m P) (z₀ ξ : ℂ)
    (horder : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun y : ℂ × ℂ => scalarExpression F.val y.1 y.2) (z₀ * Complex.exp ξ, 1) m) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun y : ℂ × ℂ => Nagata.W20.localScalar F z₀ y.1 y.2) (ξ, 0) m := by
  have hmap : AnalyticAt ℂ
      (fun y : ℂ × ℂ => (z₀ * Complex.exp y.1, Complex.exp y.2)) (ξ, 0) := by
    have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (ξ, 0)
    have hs := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (ξ, 0)
    exact (analyticAt_const.mul hf.cexp').prod hs.cexp'
  have hp : HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun y : ℂ × ℂ => scalarExpression F.val y.1 y.2)
      (z₀ * Complex.exp ξ, Complex.exp 0) m := by
    simpa only [Complex.exp_zero] using horder
  exact hp.comp (f := fun y : ℂ × ℂ => (z₀ * Complex.exp y.1, Complex.exp y.2)) hmap

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open Nagata.Workers.W17 Nagata.Workers.W28 Filter Topology

/-- Actual evaluation of an ambient normal polynomial on the chosen cubic
coordinate functions and the normal fibre coordinate. -/
noncomputable def ambientNormalScalar {σ : Type*} (X : σ → ℂ → ℂ)
    (F : Polynomial (MvPolynomial σ ℂ)) (y : ℂ × ℂ) : ℂ :=
  (F.map (MvPolynomial.eval (fun i => X i y.1))).eval y.2

/-- Coefficientwise global restriction preserves precisely the genuine local
Taylor order at every point of the punctured covering surface. -/
theorem restrictedNormalPolynomial_order_iff {σ : Type*} (X : σ → ℂ → ℂ)
    (F : Polynomial (MvPolynomial σ ℂ)) (x : ℂ × ℂ) (hx : x.1 ≠ 0) (m : ℕ) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun y : ℂ × ℂ => scalarExpression (restrictedNormalPolynomial X F) y.1 y.2) x m ↔
      HasAnalyticOrderAtLeast (𝕜 := ℂ) (ambientNormalScalar X F) x m := by
  have he : (fun y : ℂ × ℂ => scalarExpression (restrictedNormalPolynomial X F) y.1 y.2)
      =ᶠ[𝓝 x] ambientNormalScalar X F := by
    filter_upwards [continuousAt_fst.eventually_ne hx] with y hy
    exact restrictedNormalPolynomial_scalarExpression X F y.1 y.2 hy
  exact ⟨fun h => h.congr he, fun h => h.congr he.symm⟩

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open Filter Topology

/-- Ordinary analytic order is invariant under the actual period multiplier. -/
theorem automorphic_order_period {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (f : Nagata.W08.automorphicSections τ n γ) {z : ℂ} (hz : z ≠ 0) :
    analyticOrderAt f.val (τ * z) = analyticOrderAt f.val z := by
  have hscale : AnalyticAt ℂ (fun w : ℂ => τ * w) z := by fun_prop
  have hd : deriv (fun w : ℂ => τ * w) z ≠ 0 := by
    have he : deriv (fun w : ℂ => τ * w) z = τ := by
       simp
    rw [he]
    exact hτ
  have hu : AnalyticAt ℂ (fun w : ℂ => γ * w ^ (-n)) z :=
    analyticAt_const.mul (analyticAt_id.zpow hz)
  have hu0 : γ * z ^ (-n) ≠ 0 := mul_ne_zero hγ (zpow_ne_zero _ hz)
  have he : (f.val ∘ fun w : ℂ => τ * w) =ᶠ[𝓝 z]
      (fun w : ℂ => γ * w ^ (-n)) * f.val := by
    filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hz] with w hw
    exact f.property.2.2 w hw
  rw [← analyticOrderAt_comp_of_deriv_ne_zero hscale hd, analyticOrderAt_congr he,
    analyticOrderAt_mul hu (Nagata.W08.automorphicSection_analyticAt f hz),
    hu.analyticOrderAt_eq_zero.mpr hu0, zero_add]

/-- The same order holds at every representative of a marked period orbit. -/
theorem automorphic_order_orbit {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (f : Nagata.W08.automorphicSections τ n γ) {a : ℂ} (ha : a ≠ 0) (k : ℤ) :
    analyticOrderAt f.val (a * τ ^ k) = analyticOrderAt f.val a := by
  have hstep (l : ℤ) : analyticOrderAt f.val (a * τ ^ (l + 1)) =
      analyticOrderAt f.val (a * τ ^ l) := by
    rw [zpow_add₀ hτ]
    simpa only [zpow_one, mul_assoc, mul_left_comm, mul_comm] using
      automorphic_order_period hτ hγ f (mul_ne_zero ha (zpow_ne_zero _ hτ))
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => exact (hstep k).trans ih
  | pred k ih =>
      have hs := hstep (-(k : ℤ) - 1)
      convert hs.symm.trans (by simpa using ih) using 1

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.W21 Filter Topology

/-- A finite product of actual analytic functions of finite order has finite
order. Repeated zeros are allowed; no disjointness assumption is required. -/
theorem finite_product_finite_order {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (ha : ∀ i ∈ S, AnalyticAt ℂ (f i) z)
    (hf : ∀ i ∈ S, analyticOrderAt (f i) z ≠ ⊤) :
    AnalyticAt ℂ (fun w => ∏ i ∈ S, f i w) z ∧
      analyticOrderAt (fun w => ∏ i ∈ S, f i w) z ≠ ⊤ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hc : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
      simpa only [Finset.prod_empty] using And.intro hc
        (by rw [hc.analyticOrderAt_eq_zero.mpr one_ne_zero]; simp)
  | @insert i S hi ih =>
      have hai := ha i (Finset.mem_insert_self _ _)
      have hfi := hf i (Finset.mem_insert_self _ _)
      have ht := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have he : (fun w => ∏ j ∈ insert i S, f j w) = f i * (fun w => ∏ j ∈ S, f j w) := by
        funext w
        simp only [Finset.prod_insert hi, Pi.mul_apply]
      rw [he]
      refine ⟨hai.mul ht.1, ?_⟩
      rw [analyticOrderAt_mul hai ht.1]
      exact WithTop.add_ne_top.mpr ⟨hfi, ht.2⟩

/-- All actual shifted theta factors have finite order at every point of C*. -/
theorem shiftedTheta_finite_order {τ a z : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (ha : a ≠ 0) (hz : z ≠ 0) :
    AnalyticAt ℂ (fun w => thetaProduct τ (w / a)) z ∧
      analyticOrderAt (fun w => thetaProduct τ (w / a)) z ≠ ⊤ := by
  have hd : DifferentiableOn ℂ (fun w => thetaProduct τ (w / a)) {w : ℂ | w ≠ 0} :=
    fun w hw => (thetaProduct_scaled_differentiableAt hτ ha hw).differentiableWithinAt
  have han := hd.analyticAt (isOpen_ne.mem_nhds hz)
  refine ⟨han, ?_⟩
  by_cases hf : thetaProduct τ (z / a) = 0
  · rw [han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf
      (thetaProduct_scaled_zero_has_nonzero_deriv hτ hτ0 ha hz hf)]
    simp
  · rw [han.analyticOrderAt_eq_zero.mpr hf]
    simp

/-- Actual marked theta sections have finite order even with repeated marked
orbits; the finite-product proof supplies the required noncancellation. -/
theorem markedThetaSection_finite_order {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    analyticOrderAt (Nagata.W08.markedThetaSection hτ hτ0 a ha).val z ≠ ⊤ := by
  change analyticOrderAt (Nagata.W08.normalizeAtZero (markedThetaProduct τ a)) z ≠ ⊤
  rw [analyticOrderAt_congr (Nagata.W08.normalizeAtZero_eventuallyEq (markedThetaProduct τ a) hz)]
  exact (finite_product_finite_order Finset.univ (fun i w => thetaProduct τ (w / a i)) z
    (fun i _ => (shiftedTheta_finite_order hτ hτ0 (ha i) hz).1)
    (fun i _ => (shiftedTheta_finite_order hτ hτ0 (ha i) hz).2)).2

/-- Analyticity input for the genuine polynomial-basis multiplication map. -/
theorem rayMarkedSection_analyticOnNhd {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (ξ : Fin 9 → ℝ) :
    AnalyticOnNhd ℂ (Nagata.W22.rayMarkedSection hτ hτone ξ).val {z : ℂ | z ≠ 0} :=
  Nagata.W08.automorphicSection_analyticOnNhd _

/-- Finite-order input for injectivity of the genuine Pi-power map. -/
theorem rayMarkedSection_finite_order {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (ξ : Fin 9 → ℝ) {z : ℂ} (hz : z ≠ 0) :
    analyticOrderAt (Nagata.W22.rayMarkedSection hτ hτone ξ).val z ≠ ⊤ :=
  markedThetaSection_finite_order _ _ _ _ hz

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces
open scoped BigOperators

/-- The exact multiplier of the actual nine-factor section is the fixed source
scalar, retaining the odd sign and the sum of marked exponents. -/
theorem rayMarkedMultiplier {τ : ℝ} (hτ : 0 < τ) (ξ : Fin 9 → ℝ) :
    (∏ i, -((τ ^ ξ i : ℝ) : ℂ)) =
      -Nagata.Workers.W10.tauPower τ (∑ i, ξ i) := by
  rw [Finset.prod_neg]
  norm_num
  rw [Nagata.Workers.W10.tauPower, Real.rpow_sum_of_pos hτ, Complex.ofReal_prod]

end Nagata.CoefficientSpaces

end

end OAI
