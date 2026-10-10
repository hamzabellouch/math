import Mathlib
import OAI.Geometry.SmoothYau.Estimates.AnisotropicCompositionSmall
import OAI.Geometry.SmoothYau.Estimates.QuadraticInnerSpace

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open scoped LineDeriv
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalized_derivative_symbol_bound (m x : E) :
    ‖Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))‖ ≤ ‖m‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  simp only [Complex.ofReal_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity), sq_abs, inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp
  have h₂ : |inner ℝ x m| ^ 2 ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow, mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

def normalizedDerivativeSymbol (m : E) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)))
    (by
      have h : (fun x : E => Complex.ofReal
        (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))).HasTemperateGrowth := by fun_prop
      exact h.1.continuous) ‖m‖ (normalized_derivative_symbol_bound m)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_normalizedDerivativeSymbol_le (m : E) :
    ‖normalizedDerivativeSymbol m‖ ≤ ‖m‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
  exact normalized_derivative_symbol_bound m

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalizedDerivativeSymbol_hasTemperateGrowth (m : E) :
    (normalizedDerivativeSymbol m : E → ℂ).HasTemperateGrowth := by
  change (fun x : E => Complex.ofReal
    (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))).HasTemperateGrowth
  fun_prop

def sobolevDerivative (s : ℝ) (m : E) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F (s - 1) :=
  (2 * Real.pi * Complex.I) • sobolevBoundedMultiplier s (normalizedDerivativeSymbol m)

lemma norm_sobolevDerivative_le (s : ℝ) (m : E) :
    ‖sobolevDerivative (F := F) s m‖ ≤ 2 * Real.pi * ‖m‖ := by
  unfold sobolevDerivative
  rw [norm_smul]
  have hc : ‖(2 : ℂ) * Real.pi * Complex.I‖ = 2 * Real.pi := by
    simp
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sobolevBoundedMultiplier_le s _).trans (norm_normalizedDerivativeSymbol_le m)

lemma sobolevDerivative_distribution (s : ℝ) (m : E)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F (s - 1) (sobolevDerivative s m u) =
      ∂_{m} (fourierSobolevDistribution E F s u) := by
  have h : besselPotential E F (-1) (∂_{m} (fourierSobolevDistribution E F s u)) =
      fourierSobolevDistribution E F s (sobolevDerivative s m u) := by
    rw [besselPotential_neg_one_lineDerivOp_eq]
    change _ = fourierSobolevDistribution E F s
      ((2 * Real.pi * Complex.I) • sobolevBoundedMultiplier s (normalizedDerivativeSymbol m) u)
    rw [map_smul, sobolevBoundedMultiplier_distribution _ _
      (normalizedDerivativeSymbol_hasTemperateGrowth m)]
    rfl
  have h' := (besselPotential_neg_apply_eq_iff 1 _ _).mp h
  rwa [besselPotential_fourierSobolevDistribution] at h'

lemma sobolevDerivative_bound (s : ℝ) (m : E) (u : FourierSobolevSpace E F s) :
    ‖sobolevDerivative s m u‖ ≤ 2 * Real.pi * ‖m‖ * ‖u‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_sobolevDerivative_le s m) (norm_nonneg _))


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sobolevSecondDerivative (s : ℝ) (v w : E) :
    FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s - 2) :=
  sobolevDerivative (s - 1) v ∘L sobolevDerivative s w

lemma sobolevSecondDerivative_distribution (s : ℝ) (v w : E)
    (u : FourierSobolevSpace E ℂ s) :
    fourierSobolevDistribution E ℂ (s - 2) (sobolevSecondDerivative s v w u) =
      ∂_{v} (∂_{w} (fourierSobolevDistribution E ℂ s u)) := by
  have hh : s - 2 = (s - 1) - 1 := by ring
  rw [hh]
  exact (sobolevDerivative_distribution (s - 1) v _).trans
    (congrArg (fun f : 𝓢'(E, ℂ) => ∂_{v} f) (sobolevDerivative_distribution s w u))

lemma norm_sobolevSecondDerivative_le (s : ℝ) (v w : E) :
    ‖sobolevSecondDerivative s v w‖ ≤ (2 * Real.pi) ^ 2 * ‖v‖ * ‖w‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    ‖sobolevDerivative (F := ℂ) (s - 1) v‖ * ‖sobolevDerivative (F := ℂ) s w‖ ≤
        (2 * Real.pi * ‖v‖) * (2 * Real.pi * ‖w‖) :=
      mul_le_mul (norm_sobolevDerivative_le _ _) (norm_sobolevDerivative_le _ _)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

def sobolevPrincipalPerturbation {I : Type*} [Fintype I] {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2)) (v w : I → E)
    (a : I → FourierSobolevSpace E ℂ (s - 2)) :
    FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s - 2) :=
  ∑ i, (sobolevProduct hs (a i)) ∘L sobolevSecondDerivative s (v i) (w i)

lemma norm_sobolevPrincipalPerturbation_le {I : Type*} [Fintype I] {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2)) (v w : I → E)
    (a : I → FourierSobolevSpace E ℂ (s - 2)) :
    ‖sobolevPrincipalPerturbation hs v w a‖ ≤
      sobolevAlgebraConstant (E := E) (s - 2) * (2 * Real.pi) ^ 2 *
        ∑ i, ‖a i‖ * ‖v i‖ * ‖w i‖ := by
  have hC := sobolevAlgebraConstant_nonneg (E := E) (s - 2)
  apply (norm_sum_le _ _).trans
  calc
    ∑ i, ‖(sobolevProduct hs (a i)) ∘L sobolevSecondDerivative s (v i) (w i)‖ ≤
        ∑ i, sobolevAlgebraConstant (E := E) (s - 2) * ‖a i‖ *
          ((2 * Real.pi) ^ 2 * ‖v i‖ * ‖w i‖) := by
      apply Finset.sum_le_sum
      intro i _
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      apply mul_le_mul _ (norm_sobolevSecondDerivative_le _ _ _) (norm_nonneg _) (by positivity)
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro u
      exact sobolevProduct_bound hs _ _
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma sobolevPrincipalPerturbation_representative {I : Type*} [Fintype I] {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2)) (v w : I → E)
    (a : I → FourierSobolevSpace E ℂ (s - 2)) (u : FourierSobolevSpace E ℂ s) :
    sobolevRepresentative hs (sobolevPrincipalPerturbation hs v w a u) =
      ∑ i, sobolevRepresentative hs (a i) *
        sobolevRepresentative hs (sobolevSecondDerivative s (v i) (w i) u) := by
  simp only [sobolevPrincipalPerturbation, sum_apply,
    ContinuousLinearMap.comp_apply, map_sum, sobolevRepresentative_product]

theorem small_principal_elliptic_solve {I : Type*} [Fintype I] {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2)) (v w : I → E)
    (a : I → FourierSobolevSpace E ℂ (s - 2)) (α : ℝ) (hα : 1 ≤ α)
    (hq : sobolevAlgebraConstant (E := E) (s - 2) * (2 * Real.pi) ^ 2 *
      ∑ i, ‖a i‖ * ‖v i‖ * ‖w i‖ < 1)
    (f : FourierSobolevSpace E ℂ (s - 2)) :
    ∃ u : FourierSobolevSpace E ℂ s,
      α • fourierSobolevDistribution E ℂ s u - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ •
        Δ (fourierSobolevDistribution E ℂ s u) -
        fourierSobolevDistribution E ℂ (s - 2) (sobolevPrincipalPerturbation hs v w a u) =
          fourierSobolevDistribution E ℂ (s - 2) f ∧
      ‖u‖ ≤ ‖f‖ / (1 - ‖sobolevPrincipalPerturbation hs v w a‖) := by
  let P := sobolevPrincipalPerturbation hs v w a
  let R : FourierSobolevSpace E ℂ (s - 2) →L[ℂ] FourierSobolevSpace E ℂ s :=
    uniformSobolevResolvent (s - 2) α hα
  have hP : ‖P‖ < 1 := (norm_sobolevPrincipalPerturbation_le hs v w a).trans_lt hq
  have hR : ‖R‖ ≤ 1 := norm_uniformSobolevResolvent_le _ _ _
  have hRP : ‖R ∘L P‖ ≤ ‖P‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right hR (norm_nonneg P))
  have hu : Function.Bijective
      (1 - R ∘L P : FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ s) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_of_norm_lt_one (hRP.trans_lt hP))
  obtain ⟨u, hu⟩ := hu.2 (R f)
  have hfixed : u = R (f + P u) := by
    change u - R (P u) = R f at hu
    rw [map_add]
    exact sub_eq_iff_eq_add.mp hu
  refine ⟨u, ?_, ?_⟩
  · have heq := uniformSobolevResolvent_equation (s - 2) α hα (f + P u)
    have hlev : s - 2 + 2 = s := by ring
    rw [hlev] at heq
    change α • fourierSobolevDistribution E ℂ s (R (f + P u)) -
      ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • Δ (fourierSobolevDistribution E ℂ s (R (f + P u))) = _ at heq
    rw [← hfixed, map_add] at heq
    exact sub_eq_iff_eq_add.mpr heq
  · have hfu : ‖u‖ ≤ ‖f‖ + ‖P‖ * ‖u‖ := by
      calc
        ‖u‖ = ‖R (f + P u)‖ := congrArg norm hfixed
        _ ≤ ‖R‖ * ‖f + P u‖ := R.le_opNorm _
        _ ≤ ‖f + P u‖ := by simpa using
          mul_le_mul_of_nonneg_right hR (norm_nonneg (f + P u))
        _ ≤ ‖f‖ + ‖P u‖ := norm_add_le _ _
        _ ≤ ‖f‖ + ‖P‖ * ‖u‖ := add_le_add_right (P.le_opNorm u) _
    apply (le_div_iff₀ (sub_pos.mpr hP)).mpr
    nlinarith


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open scoped SchwartzMap LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma sobolevDerivative_schwartz (s : ℝ) (m : E) (f : 𝓢(E, ℂ)) :
    sobolevDerivative s m (schwartzToSobolev s f) = schwartzToSobolev (s - 1) (∂_{m} f) := by
  apply fourierSobolevDistribution_injective (s - 1)
  simp only [sobolevDerivative_distribution, schwartzToSobolev_distribution,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Set Filter
open scoped Topology LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma contDiff_sobolevRepresentative {s : ℝ} (N : ℕ)
    (hs : Module.finrank ℝ E < 2 * (s - N)) (ht : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) : ContDiff ℝ N (sobolevRepresentative ht u : E → ℂ) := by
  obtain ⟨v, hv, hvc⟩ := sobolev_Ck_representative N hs
    (fourierSobolevDistribution E ℂ s u)
    ((range_fourierSobolevDistribution s _).mp ⟨u, rfl⟩)
  have he : v = sobolevRepresentative ht u := boundedDistribution_injective
    (hv.trans (sobolevRepresentative_distribution ht u).symm)
  rwa [he] at hvc

lemma sobolevDerivative_representative {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 1))
    (ht : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) (v x : E) :
    sobolevRepresentative hs (sobolevDerivative s v u) x =
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) x v := by
  obtain ⟨w, hw, hwu⟩ := mem_closure_iff_seq_limit.mp
    ((denseRange_schwartzToSobolev (E := E) s) u)
  choose f hf using hw
  have hfu : Tendsto (fun n => schwartzToSobolev s (f n)) atTop (𝓝 u) := by
    simpa only [hf] using hwu
  have hc : Tendsto (fun n => sobolevRepresentative ht (schwartzToSobolev s (f n)))
      atTop (𝓝 (sobolevRepresentative ht u)) :=
    (sobolevRepresentative ht).continuous.continuousAt.tendsto.comp hfu
  have hd : Tendsto (fun n => sobolevRepresentative hs
      (sobolevDerivative s v (schwartzToSobolev s (f n)))) atTop
      (𝓝 (sobolevRepresentative hs (sobolevDerivative s v u))) :=
    (sobolevRepresentative hs).continuous.continuousAt.tendsto.comp
      ((sobolevDerivative s v).continuous.continuousAt.tendsto.comp hfu)
  have hc' : TendstoUniformly (fun n => (f n : E → ℂ)) (sobolevRepresentative ht u) atTop := by
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hc
    simp only [sobolevRepresentative_schwartz] at h
    convert h using 1
    ext n y
    exact (SchwartzMap.toBoundedContinuousFunction_apply _ _).symm
  have hd' : TendstoUniformly (fun n x => (∂_{v} (f n) : 𝓢(E, ℂ)) x)
      (sobolevRepresentative hs (sobolevDerivative s v u)) atTop := by
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hd
    simp only [sobolevDerivative_schwartz, sobolevRepresentative_schwartz] at h
    convert h using 1
    ext n y
    exact (SchwartzMap.toBoundedContinuousFunction_apply _ _).symm
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v |>.const_add x
  have hlim : HasDerivAt (fun t : ℝ => sobolevRepresentative ht u (x + t • v))
      (sobolevRepresentative hs (sobolevDerivative s v u) x) 0 := by
    have hh := hasDerivAt_of_tendstoUniformly
      (hd'.comp (fun t : ℝ => x + t • v))
      (Filter.Eventually.of_forall (fun n t => by
        simp only [Function.comp_def, SchwartzMap.lineDerivOp_apply,
          (f n).differentiableAt.lineDeriv_eq_fderiv]
        exact (f n).hasFDerivAt (x + t • v) |>.comp_hasDerivAt t (hline t)))
      (fun t => hc'.tendsto_at (x + t • v)) 0
    simpa only [Function.comp_def, zero_smul, add_zero, SchwartzMap.lineDerivOp_apply] using hh
  have hu := (contDiff_sobolevRepresentative 1 (by simpa using hs) ht u).differentiable
    (by norm_num)
  have hh := (hu (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 (hline 0)
  simp only [zero_smul, add_zero] at hh
  exact hlim.unique hh


open Matrix ContinuousLinearMap
open scoped InnerProductSpace

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

lemma fourierMultiplier_add {f g : E → ℂ}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) (T : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (f + g) T = fourierMultiplierCLM ℂ f T + fourierMultiplierCLM ℂ g T := by
  simp only [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.smulLeftCLM_add hf hg, _root_.add_apply,
    FourierTransform.fourierInv_add]

lemma secondDerivative_fourier (v w : E) (T : 𝓢'(E, ℂ)) :
    ∂_{v} (∂_{w} T) = -((2 * Real.pi : ℝ) ^ 2 : ℂ) •
      fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (⟪v, x⟫_ℝ * ⟪w, x⟫_ℝ)) T := by
  simp_rw [TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM, map_smul, smul_smul]
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr 1
  · push_cast
    ring_nf
    simp
  · congr 2
    ext x
    simp only [Pi.mul_apply, Complex.ofReal_mul, real_inner_comm]
    ring

def physicalQuadraticEquiv (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    E ≃L[ℝ] QuadraticInnerSpace A hA :=
  (LinearEquiv.smulOfNeZero ℝ E (2 * Real.pi) (by positivity)).toContinuousLinearEquiv.trans
    (quadraticNormEquiv b A hA)

omit [MeasurableSpace E] [BorelSpace E] in
lemma physicalQuadraticEquiv_norm_sq (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (x : E) :
    ‖physicalQuadraticEquiv b A hA x‖ ^ 2 =
      (2 * Real.pi) ^ 2 * ∑ i, ∑ j, A i j * ⟪b i, x⟫_ℝ * ⟪b j, x⟫_ℝ := by
  change ‖quadraticNormEquiv b A hA ((2 * Real.pi) • x)‖ ^ 2 = _
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow,
    quadraticNormEquiv_norm_sq]

lemma principal_fourierMultiplier (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (T : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (‖physicalQuadraticEquiv b A hA x‖ ^ 2)) T =
      - ∑ i, ∑ j, (A i j : ℂ) • (∂_{b i} (∂_{b j} T)) := by
  simp_rw [physicalQuadraticEquiv_norm_sq, Complex.ofReal_mul, Complex.ofReal_sum]
  simp only [Complex.ofReal_mul]
  have hh (i j : ι) : (fun x : E => (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ *
      Complex.ofReal ⟪b j, x⟫_ℝ).HasTemperateGrowth := by fun_prop
  have hsum : (fun x : E => ∑ i, ∑ j, (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ *
      Complex.ofReal ⟪b j, x⟫_ℝ).HasTemperateGrowth := by fun_prop
  rw [show (fun x : E => Complex.ofReal ((2 * Real.pi) ^ 2) *
      ∑ i, ∑ j, (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ * Complex.ofReal ⟪b j, x⟫_ℝ) =
      Complex.ofReal ((2 * Real.pi) ^ 2) • (fun x : E => ∑ i, ∑ j,
      (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ * Complex.ofReal ⟪b j, x⟫_ℝ) from rfl,
    TemperedDistribution.fourierMultiplierCLM_smul hsum,
    _root_.smul_apply]
  simp_rw [TemperedDistribution.fourierMultiplierCLM_sum ℂ (fun i _ =>
    Function.HasTemperateGrowth.sum fun j _ => hh i j),
    TemperedDistribution.fourierMultiplierCLM_sum ℂ (fun j _ => hh _ j),
    _root_.sum_apply, Finset.smul_sum, secondDerivative_fourier, smul_smul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show (fun x : E => (A i j : ℂ) * Complex.ofReal ⟪b i, x⟫_ℝ *
      Complex.ofReal ⟪b j, x⟫_ℝ) = (A i j : ℂ) •
      (fun x : E => Complex.ofReal (⟪b i, x⟫_ℝ * ⟪b j, x⟫_ℝ)) by
        ext x; simp; ring,
    TemperedDistribution.fourierMultiplierCLM_smul (by fun_prop),
    _root_.smul_apply, smul_smul, ← neg_smul]
  congr 1
  push_cast
  ring

lemma elliptic_fourierMultiplier (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (α : ℝ) (T : 𝓢'(E, ℂ)) :
    fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal (α + ‖physicalQuadraticEquiv b A hA x‖ ^ 2)) T =
      (α : ℂ) • T - ∑ i, ∑ j, (A i j : ℂ) • (∂_{b i} (∂_{b j} T)) := by
  rw [show (fun x : E => Complex.ofReal (α + ‖physicalQuadraticEquiv b A hA x‖ ^ 2)) =
      (fun _ => (α : ℂ)) + (fun x : E => Complex.ofReal (‖physicalQuadraticEquiv b A hA x‖ ^ 2)) by
        ext x; simp,
    fourierMultiplier_add (by fun_prop) (by
      exact Complex.hasTemperateGrowth_ofReal.comp
        ((Function.hasTemperateGrowth_norm_sq (H := QuadraticInnerSpace A hA)).comp (physicalQuadraticEquiv b A hA).toContinuousLinearMap.hasTemperateGrowth)),
    TemperedDistribution.fourierMultiplierCLM_const, _root_.smul_apply,
    ContinuousLinearMap.id_apply, principal_fourierMultiplier, sub_eq_add_neg]

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real
open scoped LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolevInclusion_representative (s t : ℝ) (h : t ≤ s)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * t)
    (u : FourierSobolevSpace E ℂ s) :
    sobolevRepresentative ht (sobolevInclusion s t h u) = sobolevRepresentative hs u := by
  apply boundedDistribution_injective
  rw [sobolevRepresentative_distribution, sobolevInclusion_distribution,
    sobolevRepresentative_distribution]

lemma fourierSobolevDistribution_congr (s t : ℝ) (h : s = t) :
    fourierSobolevDistribution E ℂ s = fourierSobolevDistribution E ℂ t := by
  subst t
  rfl

lemma sobolevRepresentative_congr (s t : ℝ) (h : s = t)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * t) :
    sobolevRepresentative hs = sobolevRepresentative ht := by
  subst t
  rfl

lemma sobolevSecondDerivative_representative {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * (s - 2)) (ht : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) (v w x : E) :
    sobolevRepresentative hs (sobolevSecondDerivative s v w u) x =
      fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y w) x v := by
  have hs1 : Module.finrank ℝ E < 2 * (s - 1) := by linarith
  have hs2 : Module.finrank ℝ E < 2 * ((s - 1) - 1) := by linarith
  have hh := sobolevDerivative_representative hs2 hs1 (sobolevDerivative s w u) v x
  have he : (sobolevRepresentative hs1 (sobolevDerivative s w u) : E → ℂ) =
      fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y w := by
    ext y
    exact sobolevDerivative_representative hs1 ht u w y
  rw [he] at hh
  have hr : sobolevRepresentative hs = sobolevRepresentative hs2 :=
    sobolevRepresentative_congr _ _ (by ring) hs hs2
  rw [sobolevSecondDerivative, ContinuousLinearMap.comp_apply, hr]
  exact hh

def frozenSobolevOperator {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (A : Matrix ι ι ℝ) (s α : ℝ) :
    FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s :=
  (α : ℂ) • sobolevInclusion (s + 2) s (by linarith) -
    ∑ i, ∑ j, (A i j : ℂ) • sobolevSecondDerivative (s + 2) (b i) (b j)

lemma frozenSobolevOperator_distribution {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (s α : ℝ) (u : FourierSobolevSpace E ℂ (s + 2)) :
    fourierSobolevDistribution E ℂ s (frozenSobolevOperator b A s α u) =
      fourierMultiplierCLM ℂ (fun x : E => Complex.ofReal
        (α + ‖physicalQuadraticEquiv b A hA x‖ ^ 2))
        (fourierSobolevDistribution E ℂ (s + 2) u) := by
  rw [elliptic_fourierMultiplier]
  simp only [frozenSobolevOperator, _root_.sub_apply,
    _root_.smul_apply, _root_.sum_apply, map_sub, map_smul, map_sum,
    sobolevInclusion_distribution]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he : fourierSobolevDistribution E ℂ (s + 2 - 2) =
      fourierSobolevDistribution E ℂ s := fourierSobolevDistribution_congr (s + 2 - 2) s (by ring)
  rw [← he]
  exact sobolevSecondDerivative_distribution (s + 2) (b i) (b j) u

lemma localEllipticInverse_sobolev_equation {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (s α : ℝ) (hα : 1 ≤ α)
    (P : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s)
    (hP : anisotropicConstant (physicalQuadraticEquiv b A hA) * ‖P‖ ≤ 1 / 2)
    (f : FourierSobolevSpace E ℂ s) :
    frozenSobolevOperator b A s α
      (localEllipticInverse (physicalQuadraticEquiv b A hA) s α hα P hP f) -
      P (localEllipticInverse (physicalQuadraticEquiv b A hA) s α hα P hP f) = f := by
  apply fourierSobolevDistribution_injective s
  rw [map_sub, frozenSobolevOperator_distribution b A hA]
  exact localEllipticInverse_equation _ s α hα P hP f

lemma frozenSobolevOperator_representative {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (A : Matrix ι ι ℝ) (s α : ℝ)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 2))
    (u : FourierSobolevSpace E ℂ (s + 2)) (x : E) :
    sobolevRepresentative hs (frozenSobolevOperator b A s α u) x =
      (α : ℂ) * sobolevRepresentative ht u x - ∑ i, ∑ j, (A i j : ℂ) *
        fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j)) x (b i) := by
  simp only [frozenSobolevOperator, _root_.sub_apply,
    _root_.smul_apply, _root_.sum_apply, map_sub, map_smul, map_sum,
    sobolevInclusion_representative _ _ _ ht hs, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hh := sobolevSecondDerivative_representative
    (s := s + 2) (by simpa only [show s + 2 - 2 = s by ring] using hs) ht u (b i) (b j) x
  rw [sobolevRepresentative_congr (s + 2 - 2) s (by ring) _ hs] at hh
  exact hh


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {s : ℝ} (h1 : Module.finrank ℝ E < 2*(s-1))
  (h0 : Module.finrank ℝ E < 2*s)
include h1 in

lemma continuous_sobolev_firstDerivative :
    Continuous (fun z : FourierSobolevSpace E ℂ s × E =>
      fderiv ℝ (sobolevRepresentative h0 z.1 : E → ℂ) z.2) := by
  apply continuous_clm_apply.mpr
  intro v
  simp_rw [← sobolevDerivative_representative h1 h0]
  exact (((sobolevRepresentative h1).continuous.comp
    (sobolevDerivative s v).continuous).comp continuous_fst).eval continuous_snd

include h1 in
lemma fderiv_real_sobolevRepresentative (u : FourierSobolevSpace E ℂ s) (x : E) :
    fderiv ℝ (fun y => (sobolevRepresentative h0 u y).re) x =
      Complex.reCLM ∘L fderiv ℝ (sobolevRepresentative h0 u : E → ℂ) x := by
  exact (Complex.reCLM.hasFDerivAt.comp x
    (((contDiff_sobolevRepresentative 1 (by simpa using h1) h0 u).differentiable
      (by norm_num)).differentiableAt.hasFDerivAt)).fderiv

include h1 in
lemma continuous_real_sobolev_firstJet :
    Continuous (fun z : FourierSobolevSpace E ℂ s × E =>
      ((sobolevRepresentative h0 z.1 z.2).re,
        fderiv ℝ (fun y => (sobolevRepresentative h0 z.1 y).re) z.2)) := by
  simp_rw [fderiv_real_sobolevRepresentative h1 h0]
  exact (Complex.continuous_re.comp
    (((sobolevRepresentative h0).continuous.comp continuous_fst).eval continuous_snd)).prodMk
      (continuous_const.clm_comp (continuous_sobolev_firstDerivative h1 h0))

end YauCounterexamples
end

end OAI
