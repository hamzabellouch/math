import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevEmbedding
import Mathlib.Analysis.Fourier.AddCircle

namespace OAI

/-!
# Continuous functions on the twelve-dimensional torus

The integer coordinates of the Euclidean frequency lattice define genuine
periodic Fourier characters. Absolute summability gives a uniformly convergent
Fourier representation, with bounded point evaluation at every torus point.
-/

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace DefocusingNLS

abbrev SchrodingerTorus := Fin 12 → AddCircle (2 * Real.pi)

instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Integer coordinates in the standard Euclidean Fourier lattice. -/
noncomputable def frequencyCoordinates (n : frequencyLattice) : Fin 12 → ℤ :=
  ((EuclideanSpace.basisFun (Fin 12) ℝ).toBasis.restrictScalars ℤ).repr n

/-- The periodic character `exp(i n·x)`. -/
noncomputable def torusCharacter (n : frequencyLattice) : C(SchrodingerTorus, ℂ) where
  toFun x := ∏ j : Fin 12, fourier (frequencyCoordinates n j) (x j)
  continuous_toFun := by fun_prop

@[simp] theorem torusCharacter_norm_apply (n : frequencyLattice) (x : SchrodingerTorus) :
    ‖torusCharacter n x‖ = 1 := by
  simp [torusCharacter, norm_prod, fourier_apply, Circle.norm_coe]

@[simp] theorem torusCharacter_zero (n : frequencyLattice) : torusCharacter n 0 = 1 := by
  simp [torusCharacter, fourier_apply]

@[simp] theorem torusCharacter_norm (n : frequencyLattice) : ‖torusCharacter n‖ = 1 := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  simp_rw [torusCharacter_norm_apply]
  exact ciSup_const

/-- A weighted Fourier coefficient times its periodic character. -/
noncomputable def sobolevTorusTerm (k : ℝ) (f : FourierL2) (n : frequencyLattice) :
    C(SchrodingerTorus, ℂ) :=
  sobolevFourierCoefficient k f n • torusCharacter n

theorem summable_sobolevTorusTerm (k : ℝ) (hk : 6 < k) (f : FourierL2) :
    Summable (sobolevTorusTerm k f) := by
  apply Summable.of_norm
  simpa [sobolevTorusTerm, norm_smul] using
    summable_norm_sobolevFourierCoefficient k hk f

/-- The actual continuous periodic function represented by a Fourier Sobolev vector. -/
noncomputable def sobolevTorusFunction (k : ℝ) (f : FourierL2) : C(SchrodingerTorus, ℂ) :=
  ∑' n, sobolevTorusTerm k f n

theorem hasSum_sobolevTorusTerm (k : ℝ) (hk : 6 < k) (f : FourierL2) :
    HasSum (sobolevTorusTerm k f) (sobolevTorusFunction k f) :=
  (summable_sobolevTorusTerm k hk f).hasSum

/-- Fourier polynomials converge uniformly on the whole twelve-torus. -/
theorem tendstoUniformly_sobolevFourierSeries (k : ℝ) (hk : 6 < k) (f : FourierL2) :
    TendstoUniformly
      (fun S : Finset frequencyLattice => fun x : SchrodingerTorus =>
        ∑ n ∈ S, sobolevFourierCoefficient k f n * torusCharacter n x)
      (sobolevTorusFunction k f) atTop := by
  have h := (ContinuousMap.isometryEquivBoundedOfCompact SchrodingerTorus ℂ).continuous.continuousAt.tendsto.comp
    (hasSum_sobolevTorusTerm k hk f)
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h
  change TendstoUniformly
    (fun S x => (∑ n ∈ S, sobolevTorusTerm k f n) x)
    (sobolevTorusFunction k f) atTop at hu
  simpa [sobolevTorusTerm, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul] using hu

/-- The modulated inverse weights representing evaluation at `x`. -/
noncomputable def sobolevPointObservationVector (k : ℝ) (hk : 6 < k)
    (x : SchrodingerTorus) : FourierL2 :=
  ⟨fun n => (((1 + ‖n‖ ^ 2) ^ (-k / 2) : ℝ) : ℂ) * conj (torusCharacter n x), by
    apply memℓp_gen
    have hs := summable_sobolev_variances 0 k (by linarith : 0 + 6 < k)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_conj,
      torusCharacter_norm_apply, mul_one, sobolev_observation_weight_sq, zero_sub] using hs⟩

/-- Point evaluation is a continuous complex-linear functional on the Fourier Sobolev model. -/
noncomputable def sobolevPointEvaluation (k : ℝ) (hk : 6 < k)
    (x : SchrodingerTorus) : FourierL2 →L[ℂ] ℂ :=
  innerSL ℂ (sobolevPointObservationVector k hk x)

theorem hasSum_sobolevPointEvaluation (k : ℝ) (hk : 6 < k)
    (x : SchrodingerTorus) (f : FourierL2) :
    HasSum (fun n => sobolevFourierCoefficient k f n * torusCharacter n x)
      (sobolevPointEvaluation k hk x f) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (sobolevPointObservationVector k hk x) f
  change HasSum (fun n => sobolevFourierCoefficient k f n * torusCharacter n x) _
  simpa [sobolevPointObservationVector, sobolevPointEvaluation, sobolevFourierCoefficient,
    RCLike.inner_apply', Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using h

/-- The continuous Fourier function agrees with bounded point evaluation. -/
theorem sobolevTorusFunction_apply (k : ℝ) (hk : 6 < k) (x : SchrodingerTorus)
    (f : FourierL2) : sobolevTorusFunction k f x = sobolevPointEvaluation k hk x f := by
  have h := (hasSum_sobolevTorusTerm k hk f).mapL
    (ContinuousMap.evalCLM (R := ℂ) x)
  have h' : HasSum (fun n => sobolevFourierCoefficient k f n * torusCharacter n x)
      (sobolevTorusFunction k f x) := by
    simpa [sobolevTorusTerm, smul_eq_mul] using h
  exact h'.unique (hasSum_sobolevPointEvaluation k hk x f)

/-- The norm of the evaluation vector does not depend on the torus point. -/
theorem sobolevPointObservationVector_norm (k : ℝ) (hk : 6 < k) (x : SchrodingerTorus) :
    ‖sobolevPointObservationVector k hk x‖ = ‖sobolevObservationVector k hk‖ := by
  have h1 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (sobolevPointObservationVector k hk x)
  have h2 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (sobolevObservationVector k hk)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2
  have heq : ‖sobolevPointObservationVector k hk x‖ ^ 2 =
      ‖sobolevObservationVector k hk‖ ^ 2 := by
    rw [h1, h2]
    congr 1
    funext n
    simp [sobolevPointObservationVector, sobolevObservationVector]
  nlinarith [norm_nonneg (sobolevPointObservationVector k hk x),
    norm_nonneg (sobolevObservationVector k hk)]

/-- The pointwise Sobolev embedding bound is uniform in `x`. -/
theorem sobolevPointEvaluation_bound (k : ℝ) (hk : 6 < k)
    (x : SchrodingerTorus) (f : FourierL2) :
    ‖sobolevPointEvaluation k hk x f‖ ≤ ‖sobolevObservationVector k hk‖ * ‖f‖ := by
  change ‖inner ℂ (sobolevPointObservationVector k hk x) f‖ ≤ _
  simpa only [sobolevPointObservationVector_norm] using
    norm_inner_le_norm (𝕜 := ℂ) (sobolevPointObservationVector k hk x) f

/-- Blowup at any point of the actual torus prevents Sobolev continuation. -/
theorem no_sobolev_extension_of_positive_point_rate
    (k : ℝ) (hk : 6 < k) (x : SchrodingerTorus) (u : ℝ → FourierL2)
    (T a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hblowup : Tendsto (fun t => (T - t) ^ a * ‖sobolevTorusFunction k (u t) x‖)
      (𝓝[<] T) (𝓝 c)) : ¬ ContinuousWithinAt u (Set.Iio T) T := by
  apply no_continuous_extension_of_positive_rescaled_norm u (sobolevPointEvaluation k hk x)
    T a c ha hc (sobolevPointEvaluation k hk x).continuous
  simpa only [sobolevTorusFunction_apply k hk] using hblowup

end DefocusingNLS

end OAI
