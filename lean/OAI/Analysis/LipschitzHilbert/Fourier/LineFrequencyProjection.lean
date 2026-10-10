import OAI.Analysis.LipschitzHilbert.Fourier.AnnularPositiveCutoff
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram
import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionEnergy
import Mathlib.Analysis.Fourier.Convolution

namespace OAI

/-! Actual smooth frequency projections on the line and their finite
square-function bound. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzProjection (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (dilatedSlopeWindow q W hW) (𝓕 f))

theorem lineSchwartzProjection_fourier (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : SchwartzMap ℝ ℂ) (eta : ℝ) :
    (𝓕 (lineSchwartzProjection q W hW f)) eta=q (W*eta)*(𝓕 f) eta := by
  simp only [lineSchwartzProjection,FourierTransform.fourier_fourierInv_eq]
  rw [SchwartzMap.smulLeftCLM_apply_apply (dilatedSlopeWindow q W hW).hasTemperateGrowth,
    dilatedSlopeWindow_apply,smul_eq_mul]

theorem lineSchwartzProjection_energy (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : ∀ eta, ‖q eta‖≤M) (f : SchwartzMap ℝ ℂ) :
    (∫ x, ‖lineSchwartzProjection q W hW f x‖^2)≤M^2*∫ x, ‖f x‖^2 := by
  rw [←SchwartzMap.integral_norm_sq_fourier (lineSchwartzProjection q W hW f),
    ←SchwartzMap.integral_norm_sq_fourier f,←integral_const_mul]
  apply integral_mono
  · exact ((𝓕 (lineSchwartzProjection q W hW f) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  · exact (((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)).const_mul _
  · intro x
    change ‖(𝓕 (lineSchwartzProjection q W hW f)) x‖^2≤M^2*‖(𝓕 f) x‖^2
    rw [lineSchwartzProjection_fourier,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM (W*x)) 2) (sq_nonneg _)

theorem lineSchwartzProjection_frame {ι : Type*} (I : Finset ι)
    (q : ι → SchwartzMap ℝ ℂ) (W : ι → ℝ) (hW : ∀ i, W i≠0)
    (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖q i (W i*eta)‖^2)≤M)
    (f : SchwartzMap ℝ ℂ) :
    (∑ i∈I, ∫ x, ‖lineSchwartzProjection (q i) (W i) (hW i) f x‖^2)≤
      M*∫ x, ‖f x‖^2 := by
  have hi (i : ι) : Integrable (fun eta =>
      ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2) :=
    ((𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hf : Integrable (fun eta => ‖(𝓕 f) eta‖^2) :=
    ((𝓕 f : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∑ i∈I, ∫ eta, ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2 :=
      Finset.sum_congr rfl (fun i _ => (SchwartzMap.integral_norm_sq_fourier _).symm)
    _ = ∫ eta, ∑ i∈I, ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2 :=
      (integral_finsetSum I (fun i _ => hi i)).symm
    _ ≤ M*∫ eta, ‖(𝓕 f) eta‖^2 := by
      rw [←integral_const_mul]
      apply integral_mono (integrable_finsetSum I (fun i _ => hi i)) (hf.const_mul M)
      intro eta
      change (∑ i∈I, ‖(𝓕 (lineSchwartzProjection (q i) (W i) (hW i) f)) eta‖^2)≤_
      simp only [lineSchwartzProjection_fourier,norm_mul,mul_pow]
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hM eta) (sq_nonneg _)
    _ = _ := by rw [SchwartzMap.integral_norm_sq_fourier]

def lineSchwartzProjectionLM (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)).toLinearMap.comp
    ((SchwartzMap.smulLeftCLM ℂ (dilatedSlopeWindow q W hW)).toLinearMap.comp
      (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)).toLinearMap)

def lineProjectionToL2 (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap.comp (lineSchwartzProjectionLM q W hW)

theorem lineProjectionToL2_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : 0≤M) (hq : ∀ eta, ‖q eta‖≤M) (f : SchwartzMap ℝ ℂ) :
    ‖lineProjectionToL2 q W hW f‖≤M*‖f.toLp 2 volume‖ := by
  have h := lineSchwartzProjection_energy q W hW M hq f
  have ho := memLp_toL2_norm_sq volume _ ((lineSchwartzProjection q W hW f).memLp 2 volume)
  have hf := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖lineProjectionToL2 q W hW f‖^2=_ at ho
  change ‖f.toLp 2 volume‖^2=_ at hf
  rw [←ho,←hf] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).1 (by simpa only [mul_pow] using h)

def lineL2Projection (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineProjectionToL2 q W hW).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

theorem lineL2Projection_onSchwartz (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (f : SchwartzMap ℝ ℂ) :
    lineL2Projection q W hW (f.toLp 2 volume)=(lineSchwartzProjection q W hW f).toLp 2 volume := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · refine ⟨SchwartzMap.seminorm ℝ 0 0 q,?_⟩
    exact lineProjectionToL2_bound q W hW _ (apply_nonneg _ _)
      (fun eta => SchwartzMap.norm_le_seminorm ℝ q eta)

theorem lineL2Projection_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (M : ℝ) (hM : 0≤M) (hq : ∀ eta, ‖q eta‖≤M) :
    ‖lineL2Projection q W hW‖≤M := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact hM
  · exact lineProjectionToL2_bound q W hW M hM hq

theorem lineL2Projection_frame {ι : Type*} (I : Finset ι)
    (q : ι → SchwartzMap ℝ ℂ) (W : ι → ℝ) (hW : ∀ i, W i≠0)
    (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖q i (W i*eta)‖^2)≤M)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∑ i∈I, ‖lineL2Projection (q i) (W i) (hW i) f‖^2)≤M*‖f‖^2 := by
  have hd : DenseRange (fun g : SchwartzMap ℝ ℂ => g.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro g
  have h := lineSchwartzProjection_frame I q W hW M hM g
  have heq (i : ι) : ‖lineL2Projection (q i) (W i) (hW i) (g.toLp 2 volume)‖^2=
      ∫ x, ‖lineSchwartzProjection (q i) (W i) (hW i) g x‖^2 := by
    rw [lineL2Projection_onSchwartz]
    exact memLp_toL2_norm_sq volume _ ((lineSchwartzProjection (q i) (W i) (hW i) g).memLp 2 volume)
  have hg : ‖g.toLp 2 volume‖^2=∫ x, ‖g x‖^2 :=
    memLp_toL2_norm_sq volume _ (g.memLp 2 volume)
  simpa only [heq,hg] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
