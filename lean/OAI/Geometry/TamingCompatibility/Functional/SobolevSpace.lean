import Mathlib

namespace OAI


noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal

namespace TamingCompatibility.HilbertSobolev

variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev H (_s : ℝ) : Type _ := Lp F 2 (volume : Measure E)

def toDistribution (s : ℝ) : H E F s →L[ℂ] 𝓢'(E,F) :=
  (besselPotential E F (-s)).comp (Lp.toTemperedDistributionCLM F volume 2)

variable {E F}

lemma lp_injective : Function.Injective
    (Lp.toTemperedDistributionCLM F (volume : Measure E) 2) := by
  exact LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot)

lemma toDistribution_injective (s : ℝ) : Function.Injective (toDistribution E F s) := by
  intro u v huv
  apply lp_injective
  have h := congrArg (besselPotential E F s) huv
  change besselPotential E F s (besselPotential E F (-s) (u : 𝓢'(E,F))) =
    besselPotential E F s (besselPotential E F (-s) (v : 𝓢'(E,F))) at h
  simpa using h

lemma bessel_toDistribution (s : ℝ) (u : H E F s) :
    besselPotential E F s (toDistribution E F s u) =
      Lp.toTemperedDistributionCLM F volume 2 u := by
  change besselPotential E F s (besselPotential E F (-s) (u : 𝓢'(E,F))) = _
  simp

lemma toDistribution_memSobolev (s : ℝ) (u : H E F s) :
    MemSobolev s 2 (toDistribution E F s u) :=
  ⟨u, bessel_toDistribution s u⟩

theorem range_toDistribution (s : ℝ) :
    Set.range (toDistribution E F s) = {u | MemSobolev s 2 u} := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact toDistribution_memSobolev s v
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change besselPotential E F (-s) (v : 𝓢'(E,F)) = u
    rw [← hv, besselPotential_besselPotential_apply]
    simp

def multiplyLp (g : Lp ℂ ∞ (volume : Measure E)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun f => g • f
      map_add' := fun f h => Lp.add_smul g f h
      map_smul' := fun c f => (Lp.smul_comm c g f).symm }
    ‖g‖ (fun f => Lp.norm_smul_le g f)

omit [CompleteSpace F] in
lemma multiplyLp_norm_le (g : Lp ℂ ∞ (volume : Measure E))
    (u : Lp F 2 (volume : Measure E)) :
    ‖multiplyLp (F := F) g u‖ ≤ ‖g‖ * ‖u‖ := Lp.norm_smul_le g u

def boundedFourierMultiplier (s : ℝ) (g : Lp ℂ ∞ (volume : Measure E)) :
    H E F s →L[ℂ] H E F s :=
  (Lp.fourierTransformₗᵢ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    multiplyLp g ∘L (Lp.fourierTransformₗᵢ E F).toContinuousLinearEquiv.toContinuousLinearMap

lemma boundedFourierMultiplier_apply (s : ℝ) (g : Lp ℂ ∞ (volume : Measure E))
    (u : H E F s) :
    boundedFourierMultiplier s g u = 𝓕⁻ (g • 𝓕 (u : Lp F 2 (volume : Measure E)) : Lp F 2 (volume : Measure E)) := rfl

lemma boundedFourierMultiplier_norm_le (s : ℝ)
    (g : Lp ℂ ∞ (volume : Measure E)) (u : H E F s) :
    ‖boundedFourierMultiplier s g u‖ ≤ ‖g‖ * ‖u‖ := by
  change ‖(Lp.fourierTransformₗᵢ E F).symm (g • 𝓕 (u : Lp F 2 (volume : Measure E)))‖ ≤ _
  rw [(Lp.fourierTransformₗᵢ E F).symm.norm_map]
  simpa only [Lp.norm_fourier_eq] using Lp.norm_smul_le g (𝓕 (u : Lp F 2 (volume : Measure E)))

lemma toLp_top_norm_le {g : E → ℂ} (hg : MemLp g ∞ (volume : Measure E))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖g x‖ ≤ C) :
    ‖hg.toLp g‖ ≤ C := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top hg.aestronglyMeasurable]
  have hle := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure E))
    (Filter.Eventually.of_forall hb)
  exact (ENNReal.toReal_mono (by finiteness) hle).trans_eq
    (ENNReal.toReal_ofReal hC)

lemma boundedFourierMultiplier_distribution (s : ℝ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hb : MemLp g ∞ (volume : Measure E))
    (u : H E F s) :
    (boundedFourierMultiplier s (hb.toLp g) u : 𝓢'(E,F)) =
      fourierMultiplierCLM F g (u : 𝓢'(E,F)) := by
  rw [boundedFourierMultiplier_apply, ← Lp.fourierInv_toTemperedDistribution_eq,
    Lp.toTemperedDistribution_smul_eq hg,
    ← Lp.fourier_toTemperedDistribution_eq]
  rfl

omit [CompleteSpace F] in
lemma bessel_fourierMultiplier_comm (s : ℝ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    besselPotential E F s (fourierMultiplierCLM F g u) =
      fourierMultiplierCLM F g (besselPotential E F s u) := by
  rw [besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply hg (by fun_prop),
    fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) hg]
  rw [mul_comm]

lemma toDistribution_boundedFourierMultiplier (s : ℝ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hb : MemLp g ∞ (volume : Measure E))
    (u : H E F s) :
    toDistribution E F s (boundedFourierMultiplier s (hb.toLp g) u) =
      fourierMultiplierCLM F g (toDistribution E F s u) := by
  change besselPotential E F (-s)
      (boundedFourierMultiplier s (hb.toLp g) u : 𝓢'(E,F)) =
    fourierMultiplierCLM F g (besselPotential E F (-s) (u : 𝓢'(E,F)))
  rw [boundedFourierMultiplier_distribution s hg hb,
    bessel_fourierMultiplier_comm (-s) hg]

def reindex (s t : ℝ) : H E F s ≃ₗᵢ[ℂ] H E F t := LinearIsometryEquiv.refl ℂ _

lemma toDistribution_reindex (s t : ℝ) (u : H E F s) :
    toDistribution E F t (reindex s t u) =
      besselPotential E F (s - t) (toDistribution E F s u) := by
  change besselPotential E F (-t) (u : 𝓢'(E,F)) =
      besselPotential E F (s - t) (besselPotential E F (-s) (u : 𝓢'(E,F)))
  rw [besselPotential_besselPotential_apply, show -s + (s - t) = -t by ring]

def weight (a : ℝ) (x : E) : ℂ := ((1 + ‖x‖ ^ 2) ^ (a / 2) : ℝ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weight_temperate (a : ℝ) : (weight (E := E) a).HasTemperateGrowth := by
  unfold weight
  fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weight_le_one {a : ℝ} (ha : a ≤ 0) (x : E) : ‖weight a x‖ ≤ 1 := by
  rw [weight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)

lemma weight_memLp_top {a : ℝ} (ha : a ≤ 0) :
    MemLp (weight (E := E) a) ∞ (volume : Measure E) :=
  memLp_top_of_bound (weight_temperate a).1.continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (weight_le_one ha))

def inclusion {s t : ℝ} (h : t ≤ s) : H E F s →L[ℂ] H E F t :=
  (reindex s t).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    boundedFourierMultiplier s ((weight_memLp_top (sub_nonpos.mpr h)).toLp _)

lemma inclusion_norm_le {s t : ℝ} (h : t ≤ s) (u : H E F s) :
    ‖inclusion h u‖ ≤ ‖u‖ := by
  change ‖boundedFourierMultiplier s
    ((weight_memLp_top (sub_nonpos.mpr h)).toLp _) u‖ ≤ ‖u‖
  refine (boundedFourierMultiplier_norm_le s _ u).trans ?_
  have hw := toLp_top_norm_le (weight_memLp_top (E := E) (sub_nonpos.mpr h))
    zero_le_one (weight_le_one (sub_nonpos.mpr h))
  simpa using mul_le_mul_of_nonneg_right hw (norm_nonneg u)

lemma toDistribution_inclusion {s t : ℝ} (h : t ≤ s) (u : H E F s) :
    toDistribution E F t (inclusion h u) = toDistribution E F s u := by
  change toDistribution E F t (reindex s t
    (boundedFourierMultiplier s ((weight_memLp_top (sub_nonpos.mpr h)).toLp _) u)) = _
  rw [toDistribution_reindex, toDistribution_boundedFourierMultiplier s
    (weight_temperate (t-s)) (weight_memLp_top (sub_nonpos.mpr h))]
  change besselPotential E F (s-t)
    (besselPotential E F (t-s) (toDistribution E F s u)) = _
  rw [besselPotential_besselPotential_apply]
  have hzero : t - s + (s - t) = 0 := by ring
  rw [hzero, besselPotential_zero, ContinuousLinearMap.id_apply]

lemma inclusion_injective {s t : ℝ} (h : t ≤ s) :
    Function.Injective (inclusion (E := E) (F := F) h) := by
  intro u v huv
  apply toDistribution_injective s
  simpa only [toDistribution_inclusion] using congrArg (toDistribution E F t) huv

end TamingCompatibility.HilbertSobolev

end

end OAI
