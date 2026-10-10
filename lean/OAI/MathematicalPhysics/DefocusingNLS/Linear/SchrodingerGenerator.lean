import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerFlow
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-!
# Two-derivative loss for the free Schrödinger evolution

In the common weighted-ℓ² model, the inclusion from `H^k` to `H^(k-2)`
multiplies by `(1+|n|²)⁻¹`. The time derivative is the bounded multiplier
`-i |n|²/(1+|n|²)`. Finite Fourier sums give the derivative of the full
flow by uniform convergence of their derivatives.
-/

open Filter Topology
open scoped ENNReal

namespace DefocusingNLS

/-- A bounded Fourier multiplier of norm at most one. -/
noncomputable def fourierContraction (m : frequencyLattice → ℂ)
    (hm : ∀ n, ‖m n‖ ≤ 1) : FourierL2 →L[ℂ] FourierL2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => m n * f n, (lp.memℓp f).mono' (by
        intro n
        rw [norm_mul]
        simpa using mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (f n)))⟩
      map_add' := by
        intro f g
        ext n
        change m n * (f n + g n) = m n * f n + m n * g n
        exact mul_add _ _ _
      map_smul' := by
        intro c f
        ext n
        change m n * (c * f n) = c * (m n * f n)
        ring }
    1 (by
      intro f
      simp only [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖m n * f n‖ ≤ ‖f n‖
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (f n)))

@[simp] theorem fourierContraction_apply (m : frequencyLattice → ℂ)
    (hm : ∀ n, ‖m n‖ ≤ 1) (f : FourierL2) (n : frequencyLattice) :
    fourierContraction m hm f n = m n * f n := rfl

/-- The continuous inclusion from `H^k` into `H^(k-2)`, in weighted coordinates. -/
noncomputable def lowerSobolevInclusion : FourierL2 →L[ℂ] FourierL2 :=
  fourierContraction (fun n => (((1 + ‖n‖ ^ 2)⁻¹ : ℝ) : ℂ)) (by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _)))

/-- The free Schrödinger generator, with the loss of two Sobolev derivatives. -/
noncomputable def lowerSobolevGenerator : FourierL2 →L[ℂ] FourierL2 :=
  fourierContraction (fun n => -Complex.I * (((‖n‖ ^ 2 / (1 + ‖n‖ ^ 2)) : ℝ) : ℂ)) (by
    intro n
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr (by linarith [sq_nonneg ‖n‖]))

@[simp] theorem lowerSobolevInclusion_apply (f : FourierL2) (n : frequencyLattice) :
    lowerSobolevInclusion f n = (((1 + ‖n‖ ^ 2)⁻¹ : ℝ) : ℂ) * f n := rfl

@[simp] theorem lowerSobolevGenerator_apply (f : FourierL2) (n : frequencyLattice) :
    lowerSobolevGenerator f n =
      -Complex.I * (((‖n‖ ^ 2 / (1 + ‖n‖ ^ 2)) : ℝ) : ℂ) * f n := rfl

/-- The inclusion changes the Sobolev index without changing physical Fourier coefficients. -/
theorem sobolevFourierCoefficient_lower_inclusion (k : ℝ) (f : FourierL2)
    (n : frequencyLattice) :
    sobolevFourierCoefficient (k - 2) (lowerSobolevInclusion f) n =
      sobolevFourierCoefficient k f n := by
  unfold sobolevFourierCoefficient
  rw [lowerSobolevInclusion_apply]
  change (((1 + ‖n‖ ^ 2) ^ (-(k - 2) / 2) : ℝ) : ℂ) *
      ((((1 + ‖n‖ ^ 2)⁻¹ : ℝ) : ℂ) * f n) =
    (((1 + ‖n‖ ^ 2) ^ (-k / 2) : ℝ) : ℂ) * f n
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_neg_one,
    ← Real.rpow_add (by positivity)]
  congr 3
  ring

/-- Applying the free group to one coordinate keeps that coordinate. -/
theorem schrodingerFlow_single (t : ℝ) (n : frequencyLattice) (c : ℂ) :
    schrodingerFlow t (lp.single 2 n c) =
      lp.single 2 n (schrodingerMultiplier t n * c) := by
  ext j
  by_cases h : j = n
  · subst j
    simp
  · simp [lp.single_apply, h]

/-- Uniform-in-time convergence of the finite Fourier approximations. -/
theorem tendstoUniformly_schrodingerFlow_partials (f : FourierL2) :
    TendstoUniformly
      (fun S : Finset frequencyLattice => fun t : ℝ =>
        ∑ n ∈ S, lp.single 2 n (schrodingerMultiplier t n * f n))
      (fun t => schrodingerFlow t f) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) f
  rw [HasSum, Metric.tendsto_nhds] at hs
  filter_upwards [hs ε hε] with S hS t
  have heq : (∑ n ∈ S, lp.single 2 n (schrodingerMultiplier t n * f n)) =
      schrodingerFlow t (∑ n ∈ S, lp.single 2 n (f n)) := by
    simp only [map_sum, schrodingerFlow_single]
  rw [heq, (schrodingerFlow t).isometry.dist_eq]
  simpa only [dist_comm] using hS

/-- The scalar phase has the exact Schrödinger derivative. -/
theorem hasDerivAt_schrodingerMultiplier_mul (n : frequencyLattice) (c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schrodingerMultiplier s n * c)
      (schrodingerMultiplier t n * (-Complex.I * ((‖n‖ ^ 2 : ℝ) : ℂ) * c)) t := by
  have h := (((((hasDerivAt_id (t : ℂ)).mul_const ((‖n‖ ^ 2 : ℝ) : ℂ)).const_mul
    (-Complex.I)).cexp).mul_const c).comp_ofReal
  simpa [schrodingerMultiplier, mul_assoc] using h

/-- Coordinatewise Schrödinger differentiation yields differentiation in ℓ²
when the derivative coordinates also form an ℓ² vector. -/
theorem hasDerivAt_schrodingerFlow_of_generator (f v : FourierL2)
    (hv : ∀ n, v n = -Complex.I * ((‖n‖ ^ 2 : ℝ) : ℂ) * f n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schrodingerFlow s f) (schrodingerFlow t v) t := by
  apply hasDerivAt_of_tendstoUniformly (tendstoUniformly_schrodingerFlow_partials v)
    (Filter.Eventually.of_forall ?_) (fun s =>
      (tendstoUniformly_schrodingerFlow_partials f).tendsto_at s) t
  intro S s
  apply HasDerivAt.fun_sum
  intro n _
  let L := (lp.singleContinuousLinearMap ℂ (fun _ : frequencyLattice => ℂ) 2 n).restrictScalars ℝ
  have h := L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_schrodingerMultiplier_mul n (f n) s)
  simpa only [hv n, L, Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    lp.singleContinuousLinearMap_apply] using h

/-- The free evolution is differentiable as an `H^(k-2)`-valued function. -/
theorem hasDerivAt_lowerSobolev_schrodingerFlow (f : FourierL2) (t : ℝ) :
    HasDerivAt (fun s => schrodingerFlow s (lowerSobolevInclusion f))
      (schrodingerFlow t (lowerSobolevGenerator f)) t := by
  apply hasDerivAt_schrodingerFlow_of_generator
  intro n
  simp only [lowerSobolevGenerator_apply, lowerSobolevInclusion_apply, Complex.ofReal_div,
    Complex.ofReal_inv]
  ring

end DefocusingNLS

end OAI
