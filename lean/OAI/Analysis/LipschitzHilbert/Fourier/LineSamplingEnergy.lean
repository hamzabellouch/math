import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingHomeomorph
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! Actual one-dimensional composition operators with uniform L2
bounds from the inverse Lipschitz estimate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem line_map_le_two (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi) :
    Measure.map phi volume≤(2:ℝ≥0∞) • (volume : Measure ℝ) := by
  apply Measure.le_iff.2
  intro S hS
  rw [Measure.map_apply hm hS,Measure.smul_apply,smul_eq_mul]
  have hh := ha.hausdorffMeasure_preimage_le (d:=1) (by norm_num) S
  simpa only [hausdorffMeasure_real,ENNReal.rpow_one,ENNReal.coe_ofNat] using hh

theorem line_memLp_comp (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume) :
    MemLp (f ∘ phi) 2 volume ∧ (∫ x, ‖f (phi x)‖^2)≤2*(∫ x, ‖f x‖^2) := by
  have hmap := line_map_le_two phi hm ha
  have hi := hf.integrable_norm_pow (by decide : 2≠0)
  have hscaled := hi.smul_measure (by norm_num : (2:ℝ≥0∞)≠⊤)
  have hcomp : Integrable (fun x => ‖f x‖^2) (Measure.map phi volume) := hscaled.mono_measure hmap
  have hint : Integrable ((fun x => ‖f x‖^2) ∘ phi) volume := hcomp.comp_measurable hm
  refine ⟨(memLp_two_iff_integrable_sq_norm (hfm.comp hm).aestronglyMeasurable).mpr hint,?_⟩
  rw [←integral_map hm.aemeasurable hcomp.aestronglyMeasurable]
  have hh := integral_mono_measure hmap (Filter.Eventually.of_forall fun x => sq_nonneg ‖f x‖) hscaled
  simpa only [integral_smul_measure,ENNReal.toReal_ofNat,smul_eq_mul] using hh

def lineCompositionToL2 (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := (line_memLp_comp phi hm ha f f.continuous.measurable (f.memLp 2 volume)).1.toLp (f ∘ phi)
  map_add' f g := (line_memLp_comp phi hm ha f f.continuous.measurable (f.memLp 2 volume)).1.toLp_add
    (line_memLp_comp phi hm ha g g.continuous.measurable (g.memLp 2 volume)).1
  map_smul' c f := (line_memLp_comp phi hm ha f f.continuous.measurable (f.memLp 2 volume)).1.toLp_const_smul c

theorem lineCompositionToL2_bound (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi)
    (f : SchwartzMap ℝ ℂ) : ‖lineCompositionToL2 phi hm ha f‖≤2*‖f.toLp 2 volume‖ := by
  have hc := line_memLp_comp phi hm ha f f.continuous.measurable (f.memLp 2 volume)
  have hn := memLp_toL2_norm_sq volume _ hc.1
  have hf := memLp_toL2_norm_sq volume f (f.memLp 2 volume)
  change ‖lineCompositionToL2 phi hm ha f‖^2=_ at hn
  change ‖f.toLp 2 volume‖^2=_ at hf
  have hh : ‖lineCompositionToL2 phi hm ha f‖^2≤2*‖f.toLp 2 volume‖^2 := by
    rw [hn,hf]
    exact hc.2
  nlinarith [norm_nonneg (lineCompositionToL2 phi hm ha f),norm_nonneg (f.toLp 2 volume)]

def lineCompositionL2 (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (lineCompositionToL2 phi hm ha).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

theorem lineCompositionL2_onSchwartz (phi : ℝ → ℝ) (hm : Measurable phi)
    (ha : AntilipschitzWith 2 phi) (f : SchwartzMap ℝ ℂ) :
    lineCompositionL2 phi hm ha (f.toLp 2 volume)=lineCompositionToL2 phi hm ha f := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · exact ⟨2,lineCompositionToL2_bound phi hm ha⟩

theorem lineCompositionL2_bound (phi : ℝ → ℝ) (hm : Measurable phi) (ha : AntilipschitzWith 2 phi) :
    ‖lineCompositionL2 phi hm ha‖≤2 := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  · norm_num
  · exact lineCompositionToL2_bound phi hm ha

end LipschitzHilbert.PacketRepresentation

end

end OAI
