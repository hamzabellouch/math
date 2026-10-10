import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplier
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.SmallSupport

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [IsFiniteMeasure μ]

def cutoff (s : Set X) (hs : MeasurableSet s) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  L2Multiplication.multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))

theorem norm_cutoff_sq (s : Set X) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    ‖cutoff (μ := μ) s hs f‖ ^ 2 = ∫ x in s, ‖f x‖ ^ 2 ∂μ := by
  have hnorm (g : Lp E 2 μ) : ‖g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    let := InnerProductSpace.rclikeToReal ℂ E
    rw [norm_sq_eq_re_inner (𝕜 := ℝ), L2.inner_def]
    simp only [RCLike.re_to_real, real_inner_self_eq_norm_sq]
  rw [hnorm, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [L2Multiplication.multiplier_indicator_coe s hs f] with x hx
  change cutoff s hs f x = _ at hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]

theorem cutoff_tendsto_apply {ι : Type*} {l : Filter ι}
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hμ : Tendsto (fun i => μ (s i)) l (𝓝 0)) (f : Lp E 2 μ) :
    Tendsto (fun i => cutoff (μ := μ) (s i) (hs i) f) l (𝓝 0) := by
  have hf : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hsq : Tendsto (fun i => ‖cutoff (μ := μ) (s i) (hs i) f‖ ^ 2) l (𝓝 0) := by
    simpa only [norm_cutoff_sq] using hf.tendsto_setIntegral_nhds_zero hμ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

theorem cutoff_tendsto_strong {ι : Type*} {l : Filter ι}
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hμ : Tendsto (fun i => μ (s i)) l (𝓝 0)) :
    Tendsto (fun i =>
      UniformConvergenceCLM.ofFun (RingHom.id ℂ) (Lp E 2 μ)
        {t : Set (Lp E 2 μ) | t.Finite} (cutoff (μ := μ) (s i) (hs i)))
      l (𝓝 0) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  intro f
  exact cutoff_tendsto_apply s hs hμ f

section SupportedErrors
variable {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem norm_error_le_of_right_supported
    (A B P : H →L[ℂ] H) {C : ℝ} (hbound : ‖A - B‖ ≤ C)
    (hsupport : (A - B) * (1 - P) = 0) (v : H) :
    ‖A v - B v‖ ≤ C * ‖P v‖ := by
  have heq : A - B = (A - B) * P := by
    simpa only [mul_sub, mul_one, sub_eq_zero] using hsupport
  have hv : A v - B v = (A - B) (P v) :=
    DFunLike.congr_fun heq v
  rw [hv]
  exact ((A - B).le_opNorm (P v)).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))

theorem tendsto_apply_of_right_supported
    {l : Filter ι} (A : ι → H →L[ℂ] H) (B : H →L[ℂ] H)
    (P : ι → H →L[ℂ] H) {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖A i - B‖ ≤ C)
    (hsupport : ∀ᶠ i in l, (A i - B) * (1 - P i) = 0)
    (hP : ∀ v, Tendsto (fun i => P i v) l (𝓝 0)) (v : H) :
    Tendsto (fun i => A i v) l (𝓝 (B v)) := by
  have hnorm : Tendsto (fun i => C * ‖P i v‖) l (𝓝 0) := by
    simpa using (hP v).norm.const_mul C
  have herr : Tendsto (fun i => A i v - B v) l (𝓝 0) := by
    apply squeeze_zero_norm' _ hnorm
    filter_upwards [hbound, hsupport] with i hi hsi
    exact norm_error_le_of_right_supported (A i) B (P i) hi hsi v
  simpa only [sub_add_cancel, zero_add] using herr.add_const (B v)

end SupportedErrors
end Invariant233.SmallSupport

end

end OAI
