import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples

variable (E F : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev FourierSobolevSpace (_s : ℝ) := Lp F 2 (volume : Measure E)

def fourierSobolevDistribution (s : ℝ) : FourierSobolevSpace E F s →L[ℂ] 𝓢'(E, F) :=
  fourierInvCLM ℂ _ ∘L
    (smulLeftCLM F (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)))) ∘L
    Lp.toTemperedDistributionCLM F volume 2

variable {E F}

lemma fourierSobolevDistribution_apply (s : ℝ) (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F s u =
      𝓕⁻ (smulLeftCLM F (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)))
        (Lp.toTemperedDistribution u)) := rfl

lemma weighted_fourier_fourierSobolevDistribution (s : ℝ)
    (u : FourierSobolevSpace E F s) :
    smulLeftCLM F (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)))
      (𝓕 (fourierSobolevDistribution E F s u)) =
        Lp.toTemperedDistribution u := by
  rw [fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  have hw : (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) *
      (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) = fun _ => 1 := by
    ext x
    simp only [Pi.mul_apply]
    norm_cast
    rw [← Real.rpow_add (by positivity)]
    convert Real.rpow_zero _ using 2
    ring
  rw [hw, smulLeftCLM_const]
  simp

lemma fourierSobolevDistribution_injective (s : ℝ) :
    Function.Injective (fourierSobolevDistribution E F s) := by
  intro u v huv
  have h := congrArg
    (fun f : 𝓢'(E, F) => smulLeftCLM F
      (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) (𝓕 f)) huv
  simp only [weighted_fourier_fourierSobolevDistribution] at h
  exact LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot h

theorem range_fourierSobolevDistribution (s : ℝ) (f : 𝓢'(E, F)) :
    (∃ u : FourierSobolevSpace E F s, fourierSobolevDistribution E F s u = f) ↔
      MemSobolev s 2 f := by
  rw [memSobolev_iff_exists_smulLeftCLM_fourier]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, weighted_fourier_fourierSobolevDistribution s u⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [fourierSobolevDistribution_apply, ← hu,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    have hw : (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) *
        (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) = fun _ => 1 := by
      ext x
      simp only [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      convert Real.rpow_zero _ using 2
      ring
    rw [hw, smulLeftCLM_const]
    simp

lemma norm_bounded_toLp_top_le (g : E →ᵇ ℂ) :
    ‖(g.memLp_top (μ := (volume : Measure E))).toLp g‖ ≤ ‖g‖ := by
  rw [Lp.norm_toLp]
  have h : eLpNorm (g : E → ℂ) ∞ (volume : Measure E) ≤ ENNReal.ofReal ‖g‖ := by
    rw [eLpNorm_exponent_top (g.memLp_top (μ := (volume : Measure E))).aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall g.norm_coe_le_norm)
  exact (ENNReal.toReal_mono (by finiteness) h).trans_eq
    (ENNReal.toReal_ofReal (norm_nonneg g))

def sobolevBoundedMultiplier (s : ℝ) (g : E →ᵇ ℂ) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F s :=
  LinearMap.mkContinuous
    { toFun := fun u => (g.memLp_top (μ := volume)).toLp g • u
      map_add' := fun u v => Lp.add_smul _ u v
      map_smul' := fun c u => (Lp.smul_comm c _ u).symm }
    ‖g‖ (fun u => (Lp.norm_smul_le _ u).trans
      (mul_le_mul_of_nonneg_right (norm_bounded_toLp_top_le g) (norm_nonneg u)))

omit [CompleteSpace F] in
lemma norm_sobolevBoundedMultiplier_le (s : ℝ) (g : E →ᵇ ℂ) :
    ‖sobolevBoundedMultiplier (F := F) s g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

lemma sobolevBoundedMultiplier_distribution (s : ℝ) (g : E →ᵇ ℂ)
    (hg : (g : E → ℂ).HasTemperateGrowth) (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F s (sobolevBoundedMultiplier s g u) =
      fourierMultiplierCLM F g (fourierSobolevDistribution E F s u) := by
  rw [fourierSobolevDistribution_apply, fourierMultiplierCLM_apply,
    fourierSobolevDistribution_apply, fourier_fourierInv_eq]
  change 𝓕⁻ (smulLeftCLM F _ (((g.memLp_top (μ := volume)).toLp g • u :
    Lp F 2 (volume : Measure E)) : 𝓢'(E, F))) = _
  rw [Lp.toTemperedDistribution_smul_eq hg,
    smulLeftCLM_smulLeftCLM_apply hg (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) hg]
  rw [mul_comm]

lemma besselPotential_fourierSobolevDistribution (s t : ℝ)
    (u : FourierSobolevSpace E F s) :
    besselPotential E F t (fourierSobolevDistribution E F s u) =
      fourierSobolevDistribution E F (s - t) u := by
  rw [besselPotential, fourierMultiplierCLM_apply, fourierSobolevDistribution_apply,
    fourier_fourierInv_eq, fourierSobolevDistribution_apply,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  congr 3
  ext x
  simp only [Pi.mul_apply]
  norm_cast
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma inverse_quadratic_hasTemperateGrowth {α : ℝ} (hα : 0 < α) :
    (fun x : E => (α + ‖x‖ ^ 2)⁻¹).HasTemperateGrowth := by
  have h : (fun x : E => α⁻¹ *
      (1 + ‖(Real.sqrt α)⁻¹ • x‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth := by
    exact (Function.HasTemperateGrowth.const (α⁻¹)).mul
      ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-1)).comp
        (((Real.sqrt α)⁻¹) • ContinuousLinearMap.id ℝ E).hasTemperateGrowth)
  convert h using 1
  ext x
  have hn : ‖(Real.sqrt α)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / α := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hα.le]
    ring
  rw [hn, Real.rpow_neg_one]
  have hd : α + ‖x‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hd' : 1 + ‖x‖ ^ 2 / α ≠ 0 := ne_of_gt (by positivity)
  field_simp

def uniformResolventSymbol (α : ℝ) (hα : 1 ≤ α) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖x‖ ^ 2)))
    (by have hp : 0 < α := lt_of_lt_of_le zero_lt_one hα
        have hd : ∀ x : E, α + ‖x‖ ^ 2 ≠ 0 := fun x => ne_of_gt (by positivity)
        fun_prop) 1 (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_le_one (by positivity)).mpr (by linarith))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma uniformResolventSymbol_hasTemperateGrowth (α : ℝ) (hα : 1 ≤ α) :
    (uniformResolventSymbol (E := E) α hα : E → ℂ).HasTemperateGrowth := by
  have h : (fun x : E => (α + ‖x‖ ^ 2)⁻¹).HasTemperateGrowth :=
    inverse_quadratic_hasTemperateGrowth (lt_of_lt_of_le zero_lt_one hα)
  change (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖x‖ ^ 2))).HasTemperateGrowth
  simp only [div_eq_mul_inv]
  fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_uniformResolventSymbol_le (α : ℝ) (hα : 1 ≤ α) :
    ‖uniformResolventSymbol (E := E) α hα‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
  intro x
  change ‖Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖x‖ ^ 2))‖ ≤ 1
  have hp : 0 < α := lt_of_lt_of_le zero_lt_one hα
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr (by linarith)

def uniformEuclideanResolvent (α : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F (fun x : E => Complex.ofReal ((α + ‖x‖ ^ 2)⁻¹))

omit [CompleteSpace F] in
lemma quadraticMultiplier_eq (α : ℝ) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F (fun x : E => Complex.ofReal (α + ‖x‖ ^ 2)) f =
      α • f - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • Δ f := by
  rw [laplacian_eq_fourierMultiplierCLM, smul_smul,
    mul_neg, inv_mul_cancel₀ (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)),
    neg_one_smul, sub_neg_eq_add]
  have heq : (fun x : E => Complex.ofReal (α + ‖x‖ ^ 2)) =
      (fun _ => Complex.ofReal α) + (fun x => Complex.ofReal (‖x‖ ^ 2)) := by
    ext x
    simp
  rw [heq, fourierMultiplierCLM_apply, smulLeftCLM_add (by fun_prop) (by fun_prop)]
  simp only [fourierInv_add, fourierMultiplierCLM_apply, add_apply,
    smulLeftCLM_const]
  rw [fourierInv_smul, fourierInv_fourier_eq, Complex.coe_smul]

omit [CompleteSpace F] in
lemma uniformEuclideanResolvent_equation {α : ℝ} (hα : 0 < α) (f : 𝓢'(E, F)) :
    α • uniformEuclideanResolvent α f - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ •
      Δ (uniformEuclideanResolvent α f) = f := by
  have hi : (fun x : E => Complex.ofReal ((α + ‖x‖ ^ 2)⁻¹)).HasTemperateGrowth :=
    (Complex.hasTemperateGrowth_ofReal).comp (inverse_quadratic_hasTemperateGrowth hα)
  rw [← quadraticMultiplier_eq, uniformEuclideanResolvent,
    fourierMultiplierCLM_fourierMultiplierCLM_apply
      hi (by fun_prop)]
  have heq : (fun x : E => Complex.ofReal ((α + ‖x‖ ^ 2)⁻¹)) *
      (fun x : E => Complex.ofReal (α + ‖x‖ ^ 2)) = fun _ => 1 := by
    ext x
    simp only [Pi.mul_apply, ← Complex.ofReal_mul]
    rw [inv_mul_cancel₀ (ne_of_gt (by positivity)), Complex.ofReal_one]
  rw [heq, fourierMultiplierCLM_const]
  simp

def uniformSobolevResolvent (s α : ℝ) (hα : 1 ≤ α) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F (s + 2) :=
  sobolevBoundedMultiplier s (uniformResolventSymbol α hα)

lemma uniformSobolevResolvent_distribution (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F (s + 2) (uniformSobolevResolvent s α hα u) =
      uniformEuclideanResolvent α (fourierSobolevDistribution E F s u) := by
  have hi : (fun x : E => Complex.ofReal ((α + ‖x‖ ^ 2)⁻¹)).HasTemperateGrowth :=
    (Complex.hasTemperateGrowth_ofReal).comp
      (inverse_quadratic_hasTemperateGrowth (lt_of_lt_of_le zero_lt_one hα))
  change fourierSobolevDistribution E F (s + 2)
    (sobolevBoundedMultiplier (s + 2) (uniformResolventSymbol α hα) u) = _
  rw [sobolevBoundedMultiplier_distribution _ _
      (uniformResolventSymbol_hasTemperateGrowth α hα),
    fourierMultiplierCLM_apply, fourierSobolevDistribution_apply,
    fourier_fourierInv_eq, uniformEuclideanResolvent,
    fourierMultiplierCLM_apply, fourierSobolevDistribution_apply,
    fourier_fourierInv_eq,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop)
      (uniformResolventSymbol_hasTemperateGrowth α hα),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop)
      hi]
  congr 3
  ext x
  change Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-(s + 2) / 2)) *
      Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖x‖ ^ 2)) =
    Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)) *
      Complex.ofReal ((α + ‖x‖ ^ 2)⁻¹)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [div_eq_mul_inv (1 + ‖x‖ ^ 2), ← mul_assoc]
  congr 1
  conv_lhs => arg 2; rw [← Real.rpow_one (1 + ‖x‖ ^ 2)]
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

omit [CompleteSpace F] in
lemma norm_uniformSobolevResolvent_le (s α : ℝ) (hα : 1 ≤ α) :
    ‖uniformSobolevResolvent (E := E) (F := F) s α hα‖ ≤ 1 :=
  (norm_sobolevBoundedMultiplier_le _ _).trans (norm_uniformResolventSymbol_le α hα)

theorem uniformSobolevResolvent_equation (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    let v := fourierSobolevDistribution E F (s + 2) (uniformSobolevResolvent s α hα u)
    α • v - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • Δ v = fourierSobolevDistribution E F s u := by
  dsimp only
  rw [uniformSobolevResolvent_distribution]
  exact uniformEuclideanResolvent_equation (lt_of_lt_of_le zero_lt_one hα) _

end YauCounterexamples

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def sobolevInclusionSymbol (s t : ℝ) (h : t ≤ s) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2)))
    (by have hh : (fun x : E => Complex.ofReal
          ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2))).HasTemperateGrowth := by fun_prop
        exact hh.1.continuous) 1 (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sobolevInclusionSymbol_hasTemperateGrowth (s t : ℝ) (h : t ≤ s) :
    (sobolevInclusionSymbol (E := E) s t h : E → ℂ).HasTemperateGrowth := by
  change (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2))).HasTemperateGrowth
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_sobolevInclusionSymbol_le (s t : ℝ) (h : t ≤ s) :
    ‖sobolevInclusionSymbol (E := E) s t h‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
  intro x
  change ‖Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2))‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)

def sobolevInclusion (s t : ℝ) (h : t ≤ s) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F t :=
  sobolevBoundedMultiplier s (sobolevInclusionSymbol s t h)

omit [CompleteSpace F] in
lemma norm_sobolevInclusion_le (s t : ℝ) (h : t ≤ s) :
    ‖sobolevInclusion (E := E) (F := F) s t h‖ ≤ 1 :=
  (norm_sobolevBoundedMultiplier_le _ _).trans (norm_sobolevInclusionSymbol_le s t h)

lemma sobolevInclusion_distribution (s t : ℝ) (h : t ≤ s)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F t (sobolevInclusion s t h u) =
      fourierSobolevDistribution E F s u := by
  change fourierSobolevDistribution E F t
    (sobolevBoundedMultiplier t (sobolevInclusionSymbol s t h) u) = _
  rw [sobolevBoundedMultiplier_distribution _ _ (sobolevInclusionSymbol_hasTemperateGrowth s t h),
    fourierMultiplierCLM_apply, fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    fourierSobolevDistribution_apply,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (sobolevInclusionSymbol_hasTemperateGrowth s t h)]
  congr 3
  ext x
  change Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-t / 2)) *
    Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((t - s) / 2)) =
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  congr 2
  ring

lemma sobolevInclusion_injective (s t : ℝ) (h : t ≤ s) :
    Function.Injective (sobolevInclusion (E := E) (F := F) s t h) := by
  intro u v hh
  apply fourierSobolevDistribution_injective s
  simpa only [sobolevInclusion_distribution] using congrArg (fourierSobolevDistribution E F t) hh

lemma sobolevInclusion_trans (s t r : ℝ) (hst : t ≤ s) (htr : r ≤ t)
    (u : FourierSobolevSpace E F s) :
    sobolevInclusion t r htr (sobolevInclusion s t hst u) =
      sobolevInclusion s r (htr.trans hst) u := by
  apply fourierSobolevDistribution_injective r
  simp only [sobolevInclusion_distribution]

def massResolventSymbol (α : ℝ) (hα : 0 < α) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : E => Complex.ofReal ((α + ‖x‖ ^ 2)⁻¹))
    (by have hh := (Complex.hasTemperateGrowth_ofReal).comp
          (inverse_quadratic_hasTemperateGrowth (E := E) hα)
        exact hh.1.continuous) α⁻¹ (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_anti₀ hα (le_add_of_nonneg_right (sq_nonneg _)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma massResolventSymbol_hasTemperateGrowth (α : ℝ) (hα : 0 < α) :
    (massResolventSymbol (E := E) α hα : E → ℂ).HasTemperateGrowth :=
  (Complex.hasTemperateGrowth_ofReal).comp (inverse_quadratic_hasTemperateGrowth hα)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_massResolventSymbol_le (α : ℝ) (hα : 0 < α) :
    ‖massResolventSymbol (E := E) α hα‖ ≤ α⁻¹ := by
  rw [BoundedContinuousFunction.norm_le (by positivity : (0 : ℝ) ≤ α⁻¹)]
  intro x
  change ‖Complex.ofReal ((α + ‖x‖ ^ 2)⁻¹)‖ ≤ α⁻¹
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_anti₀ hα (le_add_of_nonneg_right (sq_nonneg _))

def massSobolevResolvent (s α : ℝ) (hα : 0 < α) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F s :=
  sobolevBoundedMultiplier s (massResolventSymbol α hα)

omit [CompleteSpace F] in
lemma norm_massSobolevResolvent_le (s α : ℝ) (hα : 0 < α) :
    ‖massSobolevResolvent (E := E) (F := F) s α hα‖ ≤ α⁻¹ :=
  (norm_sobolevBoundedMultiplier_le _ _).trans (norm_massResolventSymbol_le α hα)

lemma massSobolevResolvent_distribution (s α : ℝ) (hα : 0 < α)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F s (massSobolevResolvent s α hα u) =
      uniformEuclideanResolvent α (fourierSobolevDistribution E F s u) :=
  sobolevBoundedMultiplier_distribution s _ (massResolventSymbol_hasTemperateGrowth α hα) u

lemma uniformSobolevResolvent_mass_bound (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    ‖sobolevInclusion (s + 2) s (by linarith) (uniformSobolevResolvent s α hα u)‖ ≤
      α⁻¹ * ‖u‖ := by
  have hp : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have heq : sobolevInclusion (s + 2) s (by linarith) (uniformSobolevResolvent s α hα u) =
      massSobolevResolvent s α hp u := by
    apply fourierSobolevDistribution_injective s
    rw [sobolevInclusion_distribution, uniformSobolevResolvent_distribution,
      massSobolevResolvent_distribution]
  rw [heq]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_massSobolevResolvent_le s α hp) (norm_nonneg u))

end YauCounterexamples

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
open scoped Real

lemma halfResolvent_scalar_bound (α t : ℝ) (hα : 1 ≤ α) (ht : 0 ≤ t) :
    (1 + t) ^ (1 / 2 : ℝ) / (α + t) ≤ (Real.sqrt α)⁻¹ := by
  have hαp : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.2 hαp
  rw [← Real.sqrt_eq_rpow, div_le_iff₀ (by positivity : 0 < α + t),
    ← div_eq_inv_mul, le_div_iff₀ hs]
  have ha := Real.sq_sqrt hαp.le
  have ht' := Real.sq_sqrt (by positivity : 0 ≤ 1 + t)
  have hsq : (Real.sqrt (1 + t) * Real.sqrt α) ^ 2 ≤ (α + t) ^ 2 := by
    rw [mul_pow, ha, ht']
    nlinarith [sq_nonneg t, mul_nonneg hαp.le ht, mul_nonneg hαp.le (sub_nonneg.mpr hα)]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def halfResolventSymbol (α : ℝ) (hα : 1 ≤ α) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖x‖ ^ 2)))
    (by
      have hh : (fun x : E => Complex.ofReal
          ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖x‖ ^ 2))).HasTemperateGrowth := by
        simp only [div_eq_mul_inv]
        exact Complex.hasTemperateGrowth_ofReal.comp
          ((by fun_prop : (fun x : E => (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)).HasTemperateGrowth).mul
            (inverse_quadratic_hasTemperateGrowth (lt_of_lt_of_le zero_lt_one hα)))
      exact hh.1.continuous)
    (Real.sqrt α)⁻¹ (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact halfResolvent_scalar_bound α _ hα (sq_nonneg _))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma halfResolventSymbol_hasTemperateGrowth (α : ℝ) (hα : 1 ≤ α) :
    (halfResolventSymbol (E := E) α hα : E → ℂ).HasTemperateGrowth := by
  change (fun x : E => Complex.ofReal
    ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖x‖ ^ 2))).HasTemperateGrowth
  simp only [div_eq_mul_inv]
  exact Complex.hasTemperateGrowth_ofReal.comp
    ((by fun_prop : (fun x : E => (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)).HasTemperateGrowth).mul
      (inverse_quadratic_hasTemperateGrowth (lt_of_lt_of_le zero_lt_one hα)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_halfResolventSymbol_le (α : ℝ) (hα : 1 ≤ α) :
    ‖halfResolventSymbol (E := E) α hα‖ ≤ (Real.sqrt α)⁻¹ := by
  rw [BoundedContinuousFunction.norm_le (by positivity : (0 : ℝ) ≤ (Real.sqrt α)⁻¹)]
  intro x
  change ‖Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖x‖ ^ 2))‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact halfResolvent_scalar_bound α _ hα (sq_nonneg _)

def halfSobolevResolvent (s α : ℝ) (hα : 1 ≤ α) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F (s + 1) :=
  sobolevBoundedMultiplier s (halfResolventSymbol α hα)

omit [CompleteSpace F] in
lemma norm_halfSobolevResolvent_le (s α : ℝ) (hα : 1 ≤ α) :
    ‖halfSobolevResolvent (E := E) (F := F) s α hα‖ ≤ (Real.sqrt α)⁻¹ :=
  (norm_sobolevBoundedMultiplier_le _ _).trans (norm_halfResolventSymbol_le α hα)

lemma halfSobolevResolvent_distribution (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F (s + 1) (halfSobolevResolvent s α hα u) =
      uniformEuclideanResolvent α (fourierSobolevDistribution E F s u) := by
  have hi : (fun x : E => Complex.ofReal ((α + ‖x‖ ^ 2)⁻¹)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp
      (inverse_quadratic_hasTemperateGrowth (lt_of_lt_of_le zero_lt_one hα))
  change fourierSobolevDistribution E F (s + 1)
      (sobolevBoundedMultiplier (s + 1) (halfResolventSymbol α hα) u) = _
  rw [sobolevBoundedMultiplier_distribution _ _ (halfResolventSymbol_hasTemperateGrowth α hα),
    fourierMultiplierCLM_apply, fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    uniformEuclideanResolvent, fourierMultiplierCLM_apply,
    fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (halfResolventSymbol_hasTemperateGrowth α hα),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) hi]
  congr 3
  ext x
  change Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-(s + 1) / 2)) *
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖x‖ ^ 2)) =
    Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)) * Complex.ofReal ((α + ‖x‖ ^ 2)⁻¹)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [div_eq_mul_inv ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) (α + ‖x‖ ^ 2),
    ← mul_assoc, ← Real.rpow_add (by positivity)]
  congr 2
  ring

lemma uniformSobolevResolvent_half_bound (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (uniformSobolevResolvent s α hα u)‖ ≤
      (Real.sqrt α)⁻¹ * ‖u‖ := by
  have heq : sobolevInclusion (s + 2) (s + 1) (by linarith) (uniformSobolevResolvent s α hα u) =
      halfSobolevResolvent s α hα u := by
    apply fourierSobolevDistribution_injective (s + 1)
    rw [sobolevInclusion_distribution, uniformSobolevResolvent_distribution,
      halfSobolevResolvent_distribution]
  rw [heq]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_halfSobolevResolvent_le s α hα) (norm_nonneg u))
end YauCounterexamples

end

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform ContDiff
variable {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def anisotropicConstant (L : E ≃L[ℝ] G) : ℝ := max 1 (‖L.symm.toContinuousLinearMap‖ ^ 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma anisotropic_norm_bound (L : E ≃L[ℝ] G) (x : E) :
    1 + ‖x‖ ^ 2 ≤ anisotropicConstant L * (1 + ‖L x‖ ^ 2) := by
  have hx : ‖x‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] using
      L.symm.toContinuousLinearMap.le_opNorm (L x)
  have hx2 := mul_self_le_mul_self (norm_nonneg x) hx
  have hC1 : 1 ≤ anisotropicConstant L := by
    unfold anisotropicConstant
    exact le_max_left 1 _
  have hCL : ‖L.symm.toContinuousLinearMap‖ ^ 2 ≤ anisotropicConstant L := le_max_right _ _
  have hb := mul_le_mul_of_nonneg_right hCL (sq_nonneg ‖L x‖)
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma anisotropic_inverse_hasTemperateGrowth (L : E ≃L[ℝ] G) {α : ℝ} (hα : 0 < α) :
    (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp
    ((inverse_quadratic_hasTemperateGrowth (E := G) hα).comp L.toContinuousLinearMap.hasTemperateGrowth)

def anisotropicResolventSymbol (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2)))
    (by have hp : 0 < α := lt_of_lt_of_le zero_lt_one hα
        have hd : ∀ x : E, α + ‖L x‖ ^ 2 ≠ 0 := fun x => ne_of_gt (by positivity)
        fun_prop) (anisotropicConstant L) (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ (by positivity : 0 < α + ‖L x‖ ^ 2)).mpr
      exact (anisotropic_norm_bound L x).trans
        (mul_le_mul_of_nonneg_left (by linarith) ((show 0 ≤ anisotropicConstant L from le_trans zero_le_one (le_max_left 1 (‖L.symm.toContinuousLinearMap‖ ^ 2))))))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma anisotropicResolventSymbol_hasTemperateGrowth (L : E ≃L[ℝ] G)
    (α : ℝ) (hα : 1 ≤ α) :
    (anisotropicResolventSymbol L α hα : E → ℂ).HasTemperateGrowth := by
  change (fun x => Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2))).HasTemperateGrowth
  have hi := anisotropic_inverse_hasTemperateGrowth L (lt_of_lt_of_le zero_lt_one hα)
  have hp : (fun x : E => Complex.ofReal (1 + ‖x‖ ^ 2)).HasTemperateGrowth := by fun_prop
  simpa only [div_eq_mul_inv, Complex.ofReal_mul] using! hp.mul hi

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_anisotropicResolventSymbol_le (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) :
    ‖anisotropicResolventSymbol L α hα‖ ≤ anisotropicConstant L := by
  apply (BoundedContinuousFunction.norm_le ((show 0 ≤ anisotropicConstant L from le_trans zero_le_one (le_max_left 1 (‖L.symm.toContinuousLinearMap‖ ^ 2))))).mpr
  intro x
  change ‖Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2))‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (by positivity : 0 < α + ‖L x‖ ^ 2)).mpr
  exact (anisotropic_norm_bound L x).trans
    (mul_le_mul_of_nonneg_left (by linarith) ((show 0 ≤ anisotropicConstant L from le_trans zero_le_one (le_max_left 1 (‖L.symm.toContinuousLinearMap‖ ^ 2)))))

def anisotropicSobolevResolvent (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F (s + 2) :=
  sobolevBoundedMultiplier s (anisotropicResolventSymbol L α hα)

omit [CompleteSpace F] in
lemma norm_anisotropicSobolevResolvent_le (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α) :
    ‖anisotropicSobolevResolvent (F := F) L s α hα‖ ≤ anisotropicConstant L :=
  (norm_sobolevBoundedMultiplier_le _ _).trans (norm_anisotropicResolventSymbol_le L α hα)

lemma anisotropicSobolevResolvent_distribution (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F (s + 2) (anisotropicSobolevResolvent L s α hα u) =
      fourierMultiplierCLM F (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹))
        (fourierSobolevDistribution E F s u) := by
  have hi := anisotropic_inverse_hasTemperateGrowth L (lt_of_lt_of_le zero_lt_one hα)
  change fourierSobolevDistribution E F (s + 2)
    (sobolevBoundedMultiplier (s + 2) (anisotropicResolventSymbol L α hα) u) = _
  rw [sobolevBoundedMultiplier_distribution _ _ (anisotropicResolventSymbol_hasTemperateGrowth L α hα),
    TemperedDistribution.fourierMultiplierCLM_apply, fourierSobolevDistribution_apply,
    fourier_fourierInv_eq, TemperedDistribution.fourierMultiplierCLM_apply, fourierSobolevDistribution_apply,
    fourier_fourierInv_eq,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (anisotropicResolventSymbol_hasTemperateGrowth L α hα),
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) hi]
  congr 3
  ext x
  change Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-(s + 2) / 2)) *
      Complex.ofReal ((1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2)) =
    Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)) * Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [div_eq_mul_inv (1 + ‖x‖ ^ 2), ← mul_assoc]
  congr 1
  conv_lhs => arg 2; rw [← Real.rpow_one (1 + ‖x‖ ^ 2)]
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

theorem anisotropicSobolevResolvent_equation (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    fourierMultiplierCLM F (fun x : E => Complex.ofReal (α + ‖L x‖ ^ 2))
      (fourierSobolevDistribution E F (s + 2) (anisotropicSobolevResolvent L s α hα u)) =
      fourierSobolevDistribution E F s u := by
  have hi := anisotropic_inverse_hasTemperateGrowth L (lt_of_lt_of_le zero_lt_one hα)
  have hq : (fun x : E => Complex.ofReal (α + ‖L x‖ ^ 2)).HasTemperateGrowth := by
    exact Complex.hasTemperateGrowth_ofReal.comp
      ((Function.HasTemperateGrowth.const α).add
        ((Function.hasTemperateGrowth_norm_sq (H := G)).comp
          L.toContinuousLinearMap.hasTemperateGrowth))
  rw [anisotropicSobolevResolvent_distribution,
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hi hq]
  have hmul : (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)) *
      (fun x : E => Complex.ofReal (α + ‖L x‖ ^ 2)) = fun _ => 1 := by
    ext x
    rw [Pi.mul_apply, ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
  rw [hmul, TemperedDistribution.fourierMultiplierCLM_const, one_smul]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma anisotropic_half_scalar_bound (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) (x : E) :
    (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2) ≤
      anisotropicConstant L * (Real.sqrt α)⁻¹ := by
  have hC : 1 ≤ anisotropicConstant L := le_max_left _ _
  have hCp : 0 ≤ anisotropicConstant L := le_trans zero_le_one hC
  have hb := anisotropic_norm_bound L x
  have hs : Real.sqrt (1 + ‖x‖ ^ 2) ≤
      anisotropicConstant L * Real.sqrt (1 + ‖L x‖ ^ 2) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have hc2 : anisotropicConstant L ≤ anisotropicConstant L ^ 2 := by nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_right hc2 (by positivity))
  rw [← Real.sqrt_eq_rpow]
  calc
    Real.sqrt (1 + ‖x‖ ^ 2) / (α + ‖L x‖ ^ 2) ≤
        (anisotropicConstant L * Real.sqrt (1 + ‖L x‖ ^ 2)) / (α + ‖L x‖ ^ 2) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ = anisotropicConstant L * ((1 + ‖L x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2)) := by
      rw [Real.sqrt_eq_rpow, mul_div_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (halfResolvent_scalar_bound α _ hα (sq_nonneg _)) hCp

def anisotropicHalfResolventSymbol (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2)))
    (by
      have hh : (fun x : E => Complex.ofReal
          ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2))).HasTemperateGrowth := by
        simp only [div_eq_mul_inv]
        exact Complex.hasTemperateGrowth_ofReal.comp
          ((by fun_prop : (fun x : E => (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)).HasTemperateGrowth).mul
            ((inverse_quadratic_hasTemperateGrowth (E := G) (lt_of_lt_of_le zero_lt_one hα)).comp L.toContinuousLinearMap.hasTemperateGrowth))
      exact hh.1.continuous)
    (anisotropicConstant L * (Real.sqrt α)⁻¹) (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact anisotropic_half_scalar_bound L α hα x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma anisotropicHalfResolventSymbol_hasTemperateGrowth (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) :
    (anisotropicHalfResolventSymbol L α hα : E → ℂ).HasTemperateGrowth := by
  change (fun x : E => Complex.ofReal
    ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2))).HasTemperateGrowth
  simp only [div_eq_mul_inv]
  exact Complex.hasTemperateGrowth_ofReal.comp
    ((by fun_prop : (fun x : E => (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)).HasTemperateGrowth).mul
      ((inverse_quadratic_hasTemperateGrowth (E := G) (lt_of_lt_of_le zero_lt_one hα)).comp L.toContinuousLinearMap.hasTemperateGrowth))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_anisotropicHalfResolventSymbol_le (L : E ≃L[ℝ] G) (α : ℝ) (hα : 1 ≤ α) :
    ‖anisotropicHalfResolventSymbol L α hα‖ ≤ (anisotropicConstant L * (Real.sqrt α)⁻¹) := by
  apply (BoundedContinuousFunction.norm_le (show 0 ≤ anisotropicConstant L * (Real.sqrt α)⁻¹ from mul_nonneg (le_trans zero_le_one (le_max_left 1 (‖L.symm.toContinuousLinearMap‖ ^ 2))) (by positivity))).mpr
  intro x
  change ‖Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2))‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact anisotropic_half_scalar_bound L α hα x

def anisotropicHalfSobolevResolvent (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α) :
    FourierSobolevSpace E F s →L[ℂ] FourierSobolevSpace E F (s + 1) :=
  sobolevBoundedMultiplier s (anisotropicHalfResolventSymbol L α hα)

omit [CompleteSpace F] in
lemma norm_anisotropicHalfSobolevResolvent_le (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α) :
    ‖anisotropicHalfSobolevResolvent (F := F) L s α hα‖ ≤ (anisotropicConstant L * (Real.sqrt α)⁻¹) :=
  (norm_sobolevBoundedMultiplier_le _ _).trans (norm_anisotropicHalfResolventSymbol_le L α hα)

lemma anisotropicHalfSobolevResolvent_distribution (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    fourierSobolevDistribution E F (s + 1) (anisotropicHalfSobolevResolvent L s α hα u) =
      fourierMultiplierCLM F (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)) (fourierSobolevDistribution E F s u) := by
  have hi : (fun x : E => Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp
      ((inverse_quadratic_hasTemperateGrowth (E := G) (lt_of_lt_of_le zero_lt_one hα)).comp L.toContinuousLinearMap.hasTemperateGrowth)
  change fourierSobolevDistribution E F (s + 1)
      (sobolevBoundedMultiplier (s + 1) (anisotropicHalfResolventSymbol L α hα) u) = _
  rw [sobolevBoundedMultiplier_distribution _ _ (anisotropicHalfResolventSymbol_hasTemperateGrowth L α hα),
    TemperedDistribution.fourierMultiplierCLM_apply, fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    TemperedDistribution.fourierMultiplierCLM_apply,
    fourierSobolevDistribution_apply, fourier_fourierInv_eq,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (anisotropicHalfResolventSymbol_hasTemperateGrowth L α hα),
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) hi]
  congr 3
  ext x
  change Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-(s + 1) / 2)) *
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) / (α + ‖L x‖ ^ 2)) =
    Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2)) * Complex.ofReal ((α + ‖L x‖ ^ 2)⁻¹)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [div_eq_mul_inv ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) (α + ‖L x‖ ^ 2),
    ← mul_assoc, ← Real.rpow_add (by positivity)]
  congr 2
  ring

lemma anisotropicSobolevResolvent_half_bound (L : E ≃L[ℝ] G) (s α : ℝ) (hα : 1 ≤ α)
    (u : FourierSobolevSpace E F s) :
    ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (anisotropicSobolevResolvent L s α hα u)‖ ≤
      (anisotropicConstant L * (Real.sqrt α)⁻¹) * ‖u‖ := by
  have heq : sobolevInclusion (s + 2) (s + 1) (by linarith) (anisotropicSobolevResolvent L s α hα u) =
      anisotropicHalfSobolevResolvent L s α hα u := by
    apply fourierSobolevDistribution_injective (s + 1)
    rw [sobolevInclusion_distribution, anisotropicSobolevResolvent_distribution,
      anisotropicHalfSobolevResolvent_distribution]
  rw [heq]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_anisotropicHalfSobolevResolvent_le L s α hα) (norm_nonneg u))

end YauCounterexamples

open Set Filter
open scoped SchwartzMap ContDiff Topology

end

end OAI
