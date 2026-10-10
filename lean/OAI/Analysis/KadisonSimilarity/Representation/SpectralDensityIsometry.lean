import OAI.Analysis.KadisonSimilarity.Representation.LocalizedL2Bound
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! Multiplication by a square-root density identifies the scalar L²
coordinates of a spectral measure with a subspace over a common base measure. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal ENNReal Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  (u : X → ℝ≥0) (hu : Measurable u)
  (hL2 : MemLp (fun x => (u x : ℂ)) 2 μ)

def squaredDensityMeasure : Measure X := μ.withDensity (fun x => ((u x) ^ 2 : ℝ≥0))

omit [T2Space X] in
include hu hL2 in
theorem weightedContinuous_memLp (f : C(X, ℂ)) :
    MemLp (fun x => (u x : ℂ) * f x) 2 μ := by
  apply hL2.of_le_mul (c := ‖f‖)
  · exact (hu.coe_nnreal_real.complex_ofReal.mul f.continuous.measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _)

def weightedContinuousVector (f : C(X, ℂ)) : Lp ℂ 2 μ :=
  (weightedContinuous_memLp μ u hu hL2 f).toLp (fun x => (u x : ℂ) * f x)

omit [T2Space X] in
theorem weightedContinuousVector_ae (f : C(X, ℂ)) :
    weightedContinuousVector μ u hu hL2 f =ᵐ[μ] (fun x => (u x : ℂ) * f x) :=
  MemLp.coeFn_toLp _

def weightedContinuousLinear : C(X, ℂ) →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := weightedContinuousVector μ u hu hL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [weightedContinuousVector_ae μ u hu hL2 (f + g),
      weightedContinuousVector_ae μ u hu hL2 f, weightedContinuousVector_ae μ u hu hL2 g,
      Lp.coeFn_add (weightedContinuousVector μ u hu hL2 f)
        (weightedContinuousVector μ u hu hL2 g)] with x hfg hf hg hs
    rw [hfg, hs]
    change _ = weightedContinuousVector μ u hu hL2 f x + weightedContinuousVector μ u hu hL2 g x
    rw [hf, hg, ContinuousMap.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [weightedContinuousVector_ae μ u hu hL2 (c • f),
      weightedContinuousVector_ae μ u hu hL2 f,
      Lp.coeFn_smul c (weightedContinuousVector μ u hu hL2 f)] with x hcf hf hs
    change weightedContinuousVector μ u hu hL2 (c • f) x =
      (c • weightedContinuousVector μ u hu hL2 f) x
    rw [hcf, hs]
    change _ = c * weightedContinuousVector μ u hu hL2 f x
    rw [hf, ContinuousMap.smul_apply]
    simp only [smul_eq_mul]
    ring

variable [IsFiniteMeasure (squaredDensityMeasure μ u)]

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [BorelSpace X] in
include hu in
theorem weight_memLp_of_finite_squareDensity :
    MemLp (fun x => (u x : ℂ)) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  have h1 : Integrable (fun _ : X => (1 : ℝ)) (squaredDensityMeasure μ u) := integrable_const 1
  have hw := (integrable_withDensity_iff_integrable_smul (hu.pow_const 2)).mp h1
  simpa only [NNReal.smul_def, smul_eq_mul, mul_one, NNReal.coe_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using hw

omit [T2Space X] in
include hu in
theorem weightedContinuous_norm (f : C(X, ℂ)) :
    ‖weightedContinuousVector μ u hu hL2 f‖ =
      ‖ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq_eq_integral, l2_norm_sq_eq_integral]
  have ha := weightedContinuousVector_ae μ u hu hL2 f
  have hb := ContinuousMap.coeFn_toLp (μ := squaredDensityMeasure μ u) (p := 2) (𝕜 := ℂ) f
  rw [integral_congr_ae (ha.mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx),
    integral_congr_ae (hb.mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)]
  rw [squaredDensityMeasure, integral_withDensity_eq_integral_smul (hu.pow_const 2)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [norm_mul, mul_pow, NNReal.smul_def, NNReal.coe_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (u x).coe_nonneg, smul_eq_mul]

def spectralDensityIsometry [ (squaredDensityMeasure μ u).WeaklyRegular] :
    Lp ℂ 2 (squaredDensityMeasure μ u) →ₗᵢ[ℂ] Lp ℂ 2 μ := by
  let F := weightedContinuousLinear μ u hu hL2
  let J := F.extendOfNorm (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ).toLinearMap
  refine ⟨J.toLinearMap, ?_⟩
  intro ξ
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
    (μ := squaredDensityMeasure μ u) (𝕜 := ℂ) (by norm_num)).induction
      (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) ξ
  obtain ⟨f, rfl⟩ := hy
  have he : J (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f) = F f := by
    apply LinearMap.extendOfNorm_eq
    · exact ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
        (μ := squaredDensityMeasure μ u) (𝕜 := ℂ) (by norm_num)
    · exact ⟨1, fun g => by
        change ‖weightedContinuousVector μ u hu hL2 g‖ ≤
          1 * ‖ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ g‖
        simpa only [one_mul] using (weightedContinuous_norm μ u hu hL2 g).le⟩
  change ‖J (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f)‖ = _
  rw [he]
  exact weightedContinuous_norm μ u hu hL2 f

theorem spectralDensityIsometry_toLp [(squaredDensityMeasure μ u).WeaklyRegular]
    (f : C(X, ℂ)) :
    spectralDensityIsometry μ u hu hL2
      (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f) =
        weightedContinuousVector μ u hu hL2 f := by
  change (weightedContinuousLinear μ u hu hL2).extendOfNorm
    (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ).toLinearMap
      (ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ f) = _
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
      (μ := squaredDensityMeasure μ u) (𝕜 := ℂ) (by norm_num)
  · refine ⟨1, fun g => ?_⟩
    change ‖weightedContinuousVector μ u hu hL2 g‖ ≤
      1 * ‖ContinuousMap.toLp 2 (squaredDensityMeasure μ u) ℂ g‖
    simpa only [one_mul] using (weightedContinuous_norm μ u hu hL2 g).le

section MeasureTransport
variable (ν : Measure X) [IsFiniteMeasure ν] [ν.WeaklyRegular]

omit [IsFiniteMeasure (squaredDensityMeasure μ u)] in
def spectralDensityIsometryOfEq (heq : squaredDensityMeasure μ u = ν) :
    Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ := by
  subst ν
  exact spectralDensityIsometry μ u hu hL2

omit [IsFiniteMeasure (squaredDensityMeasure μ u)] in
theorem spectralDensityIsometryOfEq_toLp (heq : squaredDensityMeasure μ u = ν)
    (f : C(X, ℂ)) :
    spectralDensityIsometryOfEq μ u hu hL2 ν heq (ContinuousMap.toLp 2 ν ℂ f) =
      weightedContinuousVector μ u hu hL2 f := by
  subst ν
  exact spectralDensityIsometry_toLp μ u hu hL2 f

end MeasureTransport
end KadisonSimilarity

end

end OAI
