import OAI.Analysis.LipschitzHilbert.Fourier.KernelPairing
import OAI.Analysis.LipschitzHilbert.Fourier.ShortSlopeLinearity
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! The preliminary L2 realization of the short-time operator. Its
logarithmic kernel norm is used only for continuity and density. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeOperator_schwartz_add (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator K u (f+g : SchwartzMap (ℝ×ℝ) ℂ) z=
      shortSlopeOperator K u f z+shortSlopeOperator K u g z := by
  simp only [shortSlopeOperator_eq_kernel,slopeKernelOperator,add_apply,mul_add]
  exact integral_add (slope_integrand_integrable _ (shortTimeKernel_integrable K hK) u f z)
    (slope_integrand_integrable _ (shortTimeKernel_integrable K hK) u g z)

theorem shortSlopeOperator_schwartz_smul (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (c : ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator K u (c • f : SchwartzMap (ℝ×ℝ) ℂ) z=c*shortSlopeOperator K u f z := by
  simp only [shortSlopeOperator_eq_kernel,slopeKernelOperator,smul_apply,smul_eq_mul]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem shortSchwartz_memLp (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (shortSlopeOperator K u f) 2 planeMeasure :=
  (shortSlopeOperator_energy K hKm hK u hu f f.continuous.measurable (f.memLp 2 planeMeasure)).1

def shortSchwartzToL2 (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) :
    SchwartzMap (ℝ×ℝ) ℂ →ₗ[ℂ] Lp ℂ 2 planeMeasure where
  toFun f := (shortSchwartz_memLp K hKm hK u hu f).toLp (shortSlopeOperator K u f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(shortSchwartz_memLp K hKm hK u hu (f+g)).coeFn_toLp,
      (shortSchwartz_memLp K hKm hK u hu f).coeFn_toLp,
      (shortSchwartz_memLp K hKm hK u hu g).coeFn_toLp,
      Lp.coeFn_add ((shortSchwartz_memLp K hKm hK u hu f).toLp _) ((shortSchwartz_memLp K hKm hK u hu g).toLp _)]
      with z hz hfz hgz hadd
    rw [hz,hadd]
    simp only [Pi.add_apply,hfz,hgz]
    exact shortSlopeOperator_schwartz_add K hK u f g z
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(shortSchwartz_memLp K hKm hK u hu (c • f)).coeFn_toLp,
      (shortSchwartz_memLp K hKm hK u hu f).coeFn_toLp,
      Lp.coeFn_smul c ((shortSchwartz_memLp K hKm hK u hu f).toLp _)] with z hz hfz hsmul
    simp only [RingHom.id_apply]
    rw [hz,hsmul]
    simp only [Pi.smul_apply,smul_eq_mul,hfz]
    exact shortSlopeOperator_schwartz_smul K u f c z

theorem shortSchwartzToL2_norm (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖shortSchwartzToL2 K hKm hK u hu f‖≤(2*∫ t, ‖K t‖)*‖f.toLp 2 planeMeasure‖ := by
  have he := (shortSlopeOperator_energy K hKm hK u hu f f.continuous.measurable (f.memLp 2 planeMeasure)).2
  have hout := memLp_toL2_norm_sq planeMeasure (shortSlopeOperator K u f) (shortSchwartz_memLp K hKm hK u hu f)
  have hin := memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)
  change ‖shortSchwartzToL2 K hKm hK u hu f‖^2=_ at hout
  change ‖f.toLp 2 planeMeasure‖^2=_ at hin
  rw [←hout,←hin] at he
  have hnonneg : 0≤∫ t, ‖K t‖ := integral_nonneg fun _ => norm_nonneg _
  have hsq : ‖shortSchwartzToL2 K hKm hK u hu f‖^2≤
      ((2*∫ t, ‖K t‖)*‖f.toLp 2 planeMeasure‖)^2 := by
    exact he.trans_eq (by ring)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) hnonneg) (norm_nonneg _))).1 hsq

def shortL2Operator (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  (shortSchwartzToL2 K hKm hK u hu).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure).toLinearMap

theorem shortL2Operator_onSchwartz (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    shortL2Operator K hKm hK u hu (f.toLp 2 planeMeasure)=shortSchwartzToL2 K hKm hK u hu f := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨2*∫ t, ‖K t‖,shortSchwartzToL2_norm K hKm hK u hu⟩

theorem shortL2Operator_norm (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) :
    ‖shortL2Operator K hKm hK u hu‖≤2*∫ t, ‖K t‖ := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact mul_nonneg (by norm_num) (integral_nonneg fun _ => norm_nonneg _)
  · exact shortSchwartzToL2_norm K hKm hK u hu

end LipschitzHilbert.PacketRepresentation

end

end OAI
