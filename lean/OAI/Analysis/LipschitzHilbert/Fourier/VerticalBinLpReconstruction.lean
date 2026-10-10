import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinLpEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinReconstruction

namespace OAI

/-! Reconstruction of a vertical frequency band for arbitrary L2 inputs. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

def verticalProfileLp (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W)
    (f : Lp ℂ 2 planeMeasure) : Lp ℂ 2 planeMeasure :=
  verticalConvolutionLp (verticalProfileKernel q W center)
    (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable f

theorem verticalProfileLp_continuous (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    Continuous (verticalProfileLp q W center hW) :=
  verticalConvolutionLp_continuous _ (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable

theorem verticalProfileLp_schwartz (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalProfileLp q W center hW (f.toLp 2 planeMeasure)=
      (schwartzVerticalProjection q W center f).toLp 2 planeMeasure := by
  apply Lp.ext
  have heq := verticalConvolutionLp_toLp (verticalProfileKernel q W center)
    (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)
  change verticalProfileLp q W center hW (f.toLp 2 planeMeasure)=_ at heq
  rw [heq]
  have hmem := (verticalConvolution_energy_bound (verticalProfileKernel q W center)
    (verticalProfileKernel_integrable q W center hW)
    (verticalProfileKernel_continuous q W center).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)).1
  filter_upwards [hmem.coeFn_toLp,
    (schwartzVerticalProjection q W center f).coeFn_toLp 2 planeMeasure] with z hz hz'
  rw [hz,hz',schwartzVerticalProjection_eq_convolution _ W center hW]

theorem verticalBinLp_band_reconstruction (q : SchwartzMap ℝ ℂ) (w W c C : ℝ)
    (hw : 0<w) (hW : 0<W) (hc : 0<c)
    (hq : ∀ eta, q eta≠0 → c≤eta ∧ eta≤C) (f : Lp ℂ 2 planeMeasure) :
    (∑ n∈verticalBinLabels ⌈C*W/w⌉₊ w W c C,
      verticalBinLp ⌈C*W/w⌉₊ W hW n
        (verticalBinLp ⌈C*W/w⌉₊ W hW n (verticalProfileLp q w 0 hw f)))=
      verticalProfileLp q w 0 hw f := by
  let P := fun f : Lp ℂ 2 planeMeasure =>
    (∑ n∈verticalBinLabels ⌈C*W/w⌉₊ w W c C,
      verticalBinLp ⌈C*W/w⌉₊ W hW n
        (verticalBinLp ⌈C*W/w⌉₊ W hW n (verticalProfileLp q w 0 hw f)))=
      verticalProfileLp q w 0 hw f
  apply DenseRange.induction_on (p:=P)
    (SchwartzMap.denseRange_toLpCLM (E:=ℝ×ℝ) (F:=ℂ) (μ:=planeMeasure)
      (by norm_num : (2:ℝ≥0∞)≠⊤)) f
  · apply isClosed_eq
    · apply continuous_finsetSum
      intro n hn
      exact (verticalBinLp_continuous _ W hW n).comp
        ((verticalBinLp_continuous _ W hW n).comp (verticalProfileLp_continuous q w 0 hw))
    · exact verticalProfileLp_continuous q w 0 hw
  · intro g
    dsimp only [P]
    simp only [SchwartzMap.toLpCLM_apply,verticalProfileLp_schwartz,verticalBinLp_schwartz]
    have hband : ∀ omega, planarFourier (schwartzVerticalProjection q w 0 g) omega≠0 →
        c≤w*omega.2 ∧ w*omega.2≤C := by
      intro omega ho
      rw [schwartzVerticalProjection_fourier] at ho
      have hnonzero : q (w*(omega.2-0))≠0 := left_ne_zero_of_mul ho
      simpa only [sub_zero] using hq _ hnonzero
    have hrec := verticalBin_schwartz_reconstruction (schwartzVerticalProjection q w 0 g)
      w W c C hw hW hc hband
    have ht := congrArg (fun h : SchwartzMap (ℝ×ℝ) ℂ =>
      SchwartzMap.toLpCLM ℝ ℂ 2 planeMeasure h) hrec
    simpa only [map_sum,SchwartzMap.toLpCLM_apply] using ht

end LipschitzHilbert.PacketRepresentation

end

end OAI
