import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedBandProjection
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticePolarizationSpectrum
import OAI.Analysis.LipschitzHilbert.Estimates.ShortL2Operator

namespace OAI

/-! The actual vertical Schwartz multiplier extends to L2. This
preliminary bound supplies continuity for restricted-test approximation. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def schwartzVerticalProjectionLM (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    SchwartzMap (ℝ×ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ×ℝ) ℂ where
  toFun := schwartzVerticalProjection p w 0
  map_add' f g := by
    apply planar_schwartz_ext_fourier
    intro omega
    simp only [schwartzVerticalProjection_fourier,planarFourier_add]
    ring
  map_smul' c f := by
    apply planar_schwartz_ext_fourier
    intro omega
    simp only [schwartzVerticalProjection_fourier,planarFourier_smul,RingHom.id_apply]
    ring

def verticalSchwartzToL2 (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    SchwartzMap (ℝ×ℝ) ℂ →ₗ[ℂ] Lp ℂ 2 planeMeasure :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure).toLinearMap.comp (schwartzVerticalProjectionLM p w)

theorem verticalSchwartzToL2_norm (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖verticalSchwartzToL2 p w f‖≤verticalProjectionCost p*‖f.toLp 2 planeMeasure‖ := by
  let K := verticalProfileKernel p w 0
  let A := ∫ s, ‖(𝓕⁻ p : SchwartzMap ℝ ℂ) s‖
  have hKm : Measurable K := by
    unfold K verticalProfileKernel modulatedTimeKernel scaledTimeKernel
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (continuous_const.mul ((𝓕⁻ p : SchwartzMap ℝ ℂ).continuous.comp (by fun_prop)))).measurable
  have hKi : Integrable K := modulatedTimeKernel_integrable (𝓕⁻ p) w 0 hw
  have he := (verticalConvolution_energy_bound K hKi hKm f f.continuous.measurable
    (f.memLp 2 planeMeasure)).2
  have hid : verticalConvolution K f=schwartzVerticalProjection p w 0 f := by
    funext z
    exact (schwartzVerticalProjection_eq_convolution p w 0 hw f z).symm
  have hmass : (∫ s, ‖K s‖)=A := modulatedTimeKernel_l1 (𝓕⁻ p) w 0 hw
  rw [hid,hmass] at he
  have hout := memLp_toL2_norm_sq planeMeasure (schwartzVerticalProjection p w 0 f)
    ((schwartzVerticalProjection p w 0 f).memLp 2 planeMeasure)
  have hin := memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)
  change ‖verticalSchwartzToL2 p w f‖^2=_ at hout
  change ‖f.toLp 2 planeMeasure‖^2=_ at hin
  rw [←hout,←hin] at he
  have hA : 0≤A := integral_nonneg fun _ => norm_nonneg _
  have hAC : A≤verticalProjectionCost p := by
    change A≤1+A
    linarith only [hA]
  have hsquare : ‖verticalSchwartzToL2 p w f‖^2≤
      (verticalProjectionCost p*‖f.toLp 2 planeMeasure‖)^2 := by
    apply he.trans
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAC 2) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (verticalProjectionCost_pos p).le (norm_nonneg _))).1 hsquare

def verticalL2Projection (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  (verticalSchwartzToL2 p w).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure).toLinearMap

theorem verticalL2Projection_onSchwartz (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalL2Projection p w (f.toLp 2 planeMeasure)=(schwartzVerticalProjection p w 0 f).toLp 2 planeMeasure := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨verticalProjectionCost p,verticalSchwartzToL2_norm p w hw⟩

theorem verticalL2Projection_norm (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w) :
    ‖verticalL2Projection p w‖≤verticalProjectionCost p := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact (verticalProjectionCost_pos p).le
  · exact verticalSchwartzToL2_norm p w hw

end LipschitzHilbert.PacketRepresentation

end

end OAI
