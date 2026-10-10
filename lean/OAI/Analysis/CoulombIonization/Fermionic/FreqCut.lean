import Mathlib
import OAI.Analysis.CoulombIonization.Variational.IntegralFourierInvMul

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombLT

section
open CoulombAtom Metric
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma l2_norm_sq_eq_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K]
  change (∫ x, (‖f x‖ : ℂ)^2 ∂μ).re = _
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  rfl

lemma l2_ball_integrable (f : Lp ℂ 2 (volume : Measure V)) (R : ℝ) :
    Integrable ((ball 0 R).indicator (fun ξ => f ξ)) := by
  have : IsFiniteMeasure ((volume : Measure V).restrict (ball 0 R)) :=
    ⟨by simpa using measure_ball_lt_top (x := (0:V)) (r := R)⟩
  apply IntegrableOn.integrable_indicator _ measurableSet_ball
  exact memLp_one_iff_integrable.mp (((Lp.memLp f).restrict (ball 0 R)).mono_exponent (by norm_num))

def freqCut (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) : Lp ℂ 2 (volume : Measure V) :=
  ((Lp.memLp f).indicator (measurableSet_ball (x := (0:V)) (ε := R))).toLp ((ball 0 R).indicator (fun ξ => f ξ))

lemma freqCut_ae (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    (fun ξ => freqCut R f ξ) =ᵐ[volume] (ball 0 R).indicator (fun ξ => f ξ) :=
  ((Lp.memLp f).indicator (measurableSet_ball (x := (0:V)) (ε := R))).coeFn_toLp

def lowPart (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) (x : V) : ℂ :=
  𝓕⁻ ((ball 0 R).indicator (fun ξ => (𝓕 f : Lp ℂ 2 volume) ξ)) x

lemma lowPart_continuous (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    Continuous (lowPart R f) := by
  change Continuous (𝓕⁻ ((ball 0 R).indicator (fun ξ => (𝓕 f : Lp ℂ 2 volume) ξ)))
  have he : 𝓕⁻ ((ball 0 R).indicator (fun ξ => (𝓕 f : Lp ℂ 2 volume) ξ)) =
      fun x => 𝓕 ((ball 0 R).indicator (fun ξ => (𝓕 f : Lp ℂ 2 volume) ξ)) (-x) :=
    funext (Real.fourierInv_eq_fourier_neg _)
  rw [he]
  exact (classical_fourier_continuous (l2_ball_integrable (𝓕 f) R)).comp continuous_neg

lemma lowPart_ae (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    (fun x => (𝓕⁻ (freqCut R (𝓕 f)) : Lp ℂ 2 volume) x) =ᵐ[volume] lowPart R f :=
  l2_fourierInv_ae_classical ((Lp.memLp (𝓕 f)).indicator (measurableSet_ball (x := (0:V)) (ε := R)))
    (l2_ball_integrable (𝓕 f) R)

lemma freqCut_norm_sq (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    ‖freqCut R f‖^2 = ∫ ξ in ball 0 R, ‖f ξ‖^2 := by
  rw [l2_norm_sq_eq_integral, ← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [((Lp.memLp f).indicator (measurableSet_ball (x := (0:V)) (ε := R))).coeFn_toLp] with x hx
  change ‖((Lp.memLp f).indicator (measurableSet_ball (x := (0:V)) (ε := R))).toLp _ x‖^2 = _
  rw [hx]
  by_cases h : x ∈ ball (0:V) R <;> simp [h]

lemma highPart_norm_sq (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    (∫ x, ‖f x - lowPart R f x‖^2) =
      ∫ ξ in (ball 0 R)ᶜ, ‖(𝓕 f : Lp ℂ 2 volume) ξ‖^2 := by
  have hi : (fun x => (f - 𝓕⁻ (freqCut R (𝓕 f)) : Lp ℂ 2 volume) x) =ᵐ[volume]
      (fun x => f x - lowPart R f x) := by
    filter_upwards [Lp.coeFn_sub f (𝓕⁻ (freqCut R (𝓕 f))), lowPart_ae R f] with x hx hy
    simpa only [Pi.sub_apply,hy] using hx
  calc
    _ = ‖f - 𝓕⁻ (freqCut R (𝓕 f))‖^2 := by
      rw [l2_norm_sq_eq_integral]
      exact integral_congr_ae (hi.symm.fun_comp (fun z => ‖z‖^2))
    _ = ‖(𝓕 f : Lp ℂ 2 volume) - freqCut R (𝓕 f)‖^2 := by
      rw [← Lp.norm_fourier_eq]
      change ‖(Lp.fourierTransformₗᵢ V ℂ) (f - 𝓕⁻ (freqCut R (𝓕 f)))‖^2 = _
      rw [map_sub]
      change ‖(𝓕 f : Lp ℂ 2 volume) - 𝓕 (𝓕⁻ (freqCut R (𝓕 f)))‖^2 = _
      rw [FourierInvPair.fourier_fourierInv_eq]
    _ = _ := by
      rw [l2_norm_sq_eq_integral, ← integral_indicator measurableSet_ball.compl]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (𝓕 f) (freqCut R (𝓕 f)),
        freqCut_ae R (𝓕 f)] with x hx hy
      simp only [Pi.sub_apply] at hx
      rw [hx]
      rw [hy]
      by_cases h : x ∈ ball (0:V) R <;> simp [h]
end

open CoulombAtom Metric ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def kernelFunction (R : ℝ) (x : V) (ξ : V) : ℂ :=
  (ball 0 R).indicator (fun ξ => conj ((Real.fourierChar (inner ℝ ξ x) : Circle) : ℂ)) ξ

lemma kernelFunction_memLp (R : ℝ) (x : V) : MemLp (kernelFunction R x) 2 := by
  have : IsFiniteMeasure ((volume : Measure V).restrict (ball 0 R)) :=
    ⟨by simpa using measure_ball_lt_top (x := (0:V)) (r := R)⟩
  apply (memLp_indicator_iff_restrict measurableSet_ball).2
  have hc : Continuous (fun ξ : V => conj ((Real.fourierChar (inner ℝ ξ x) : Circle) : ℂ)) := by
    fun_prop
  exact (memLp_const (μ := (volume : Measure V).restrict (ball 0 R)) (1:ℝ)).congr_norm
    hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by simp [Circle.norm_coe])

def lowKernel (R : ℝ) (x : V) : Lp ℂ 2 (volume : Measure V) :=
  (kernelFunction_memLp R x).toLp _

lemma lowKernel_norm_sq (R : ℝ) (x : V) :
    ‖lowKernel R x‖^2 = (volume : Measure V).real (ball 0 R) := by
  rw [l2_norm_sq_eq_integral]
  have he : (fun ξ => ‖lowKernel R x ξ‖^2) =ᵐ[volume]
      (ball 0 R).indicator (fun _ => (1:ℝ)) := by
    filter_upwards [(kernelFunction_memLp R x).coeFn_toLp] with ξ hξ
    change ‖(kernelFunction_memLp R x).toLp _ ξ‖^2 = _
    rw [hξ]
    by_cases h : ξ ∈ ball (0:V) R <;> simp [kernelFunction,h,Circle.norm_coe]
  rw [integral_congr_ae he,integral_indicator measurableSet_ball,integral_const]
  simp [Measure.real]

lemma lowPart_eq_inner (R : ℝ) (f : Lp ℂ 2 (volume : Measure V)) (x : V) :
    lowPart R f x = inner ℂ (lowKernel R x) (𝓕 f) := by
  rw [lowPart,Real.fourierInv_eq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(kernelFunction_memLp R x).coeFn_toLp] with ξ hξ
  change _ = inner ℂ ((kernelFunction_memLp R x).toLp _ ξ) _
  rw [hξ,RCLike.inner_apply]
  by_cases h : ξ ∈ ball (0:V) R <;>
    simp [kernelFunction,h,Circle.smul_def,smul_eq_mul,mul_comm]

variable {ι : Type*} [Fintype ι]

def BesselFamily (f : ι → Lp ℂ 2 (volume : Measure V)) : Prop :=
  ∀ u, (∑ j, ‖inner ℂ u (f j)‖^2) ≤ ‖u‖^2

lemma BesselFamily.fourier {f : ι → Lp ℂ 2 (volume : Measure V)}
    (hf : BesselFamily f) : BesselFamily (fun j => 𝓕 (f j)) := by
  intro u
  have h := hf (𝓕⁻ u)
  have hi (j) : inner ℂ u (𝓕 (f j)) = inner ℂ (𝓕⁻ u) (f j) := by
    simpa only [FourierInvPair.fourier_fourierInv_eq] using (Lp.inner_fourier_eq (𝓕⁻ u) (f j))
  have hn : ‖(𝓕⁻ u : Lp ℂ 2 volume)‖ = ‖u‖ := by
    simpa only [FourierInvPair.fourier_fourierInv_eq] using (Lp.norm_fourier_eq (𝓕⁻ u)).symm
  simpa only [hi,hn] using h

lemma BesselFamily.low_bound {f : ι → Lp ℂ 2 (volume : Measure V)}
    (hf : BesselFamily f) (R : ℝ) (x : V) :
    (∑ j, ‖lowPart R (f j) x‖^2) ≤ (volume : Measure V).real (ball 0 R) := by
  simpa only [lowPart_eq_inner,lowKernel_norm_sq] using hf.fourier (lowKernel R x)

lemma family_density_split (f : ι → Lp ℂ 2 (volume : Measure V)) (R : ℝ) (x : V) :
    (∑ j, ‖f j x‖^2) ≤ 2*(∑ j, ‖lowPart R (f j) x‖^2) +
      2*(∑ j, ‖f j x - lowPart R (f j) x‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h : ‖f j x‖ ≤ ‖lowPart R (f j) x‖ + ‖f j x - lowPart R (f j) x‖ := by
    convert norm_add_le (lowPart R (f j) x) (f j x - lowPart R (f j) x) using 1; abel_nf
  have hs := pow_le_pow_left₀ (norm_nonneg (f j x)) h 2
  nlinarith [sq_nonneg (‖lowPart R (f j) x‖ - ‖f j x - lowPart R (f j) x‖)]
end CoulombLT

open MeasureTheory Filter
open scoped ENNReal

end

end OAI
