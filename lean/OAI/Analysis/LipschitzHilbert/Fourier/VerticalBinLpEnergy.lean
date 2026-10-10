import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalConvolutionLp
import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarGramSchur

namespace OAI

/-! The finite bin square-function bound on the actual L2 quotient. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProfileKernel_continuous (q : SchwartzMap ℝ ℂ) (W center : ℝ) :
    Continuous (verticalProfileKernel q W center) := by
  unfold verticalProfileKernel modulatedTimeKernel scaledTimeKernel
  fun_prop


theorem verticalProfileKernel_integrable (q : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    Integrable (verticalProfileKernel q W center) :=
  modulatedTimeKernel_integrable (𝓕⁻ q : SchwartzMap ℝ ℂ) W center hW

def verticalBinLp (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ)
    (f : Lp ℂ 2 planeMeasure) : Lp ℂ 2 planeMeasure :=
  verticalConvolutionLp (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable f

theorem verticalBinLp_continuous (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ) :
    Continuous (verticalBinLp K W hW n) :=
  verticalConvolutionLp_continuous _
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable

theorem verticalBinLp_schwartz (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    verticalBinLp K W hW n (f.toLp 2 planeMeasure)=
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter K W n) f).toLp 2
        planeMeasure := by
  apply Lp.ext
  have hi := verticalConvolutionLp_toLp
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)
  change verticalBinLp K W hW n (f.toLp 2 planeMeasure)=_ at hi
  rw [hi]
  have hmem := (verticalConvolution_energy_bound
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable verticalBinProfile W (verticalBinCenter K W n) hW)
    (verticalProfileKernel_continuous _ _ _).measurable f f.continuous.measurable
    (f.memLp 2 planeMeasure)).1
  filter_upwards [MemLp.coeFn_toLp hmem,
    (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter K W n) f).coeFn_toLp
      2 planeMeasure] with z hz hz'
  rw [hz,hz',schwartzVerticalProjection_eq_convolution _ W _ hW]

theorem verticalBinLp_energy (K : ℕ) (W : ℝ) (hW : 0<W) (I : Finset ℕ)
    (hI : I⊆Finset.range (2*K+1)) (f : Lp ℂ 2 planeMeasure) :
    (∑ n∈I, ‖verticalBinLp K W hW n f‖^2)≤‖f‖^2 := by
  let P := fun f : Lp ℂ 2 planeMeasure => (∑ n∈I, ‖verticalBinLp K W hW n f‖^2)≤‖f‖^2
  apply DenseRange.induction_on (p:=P)
    (SchwartzMap.denseRange_toLpCLM (E:=ℝ×ℝ) (F:=ℂ) (μ:=planeMeasure)
      (by norm_num : (2:ℝ≥0∞)≠⊤)) f
  · apply isClosed_le
    · exact continuous_finsetSum _ (fun n _ => ((verticalBinLp_continuous K W hW n).norm).pow 2)
    · exact continuous_norm.pow 2
  · intro g
    dsimp only [P]
    simp only [SchwartzMap.toLpCLM_apply,verticalBinLp_schwartz]
    simp_rw [planar_toL2_norm_sq]
    exact verticalBin_schwartz_energy_le g K W hW I hI

theorem verticalBin_measurable_energy (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) (K : ℕ) (W : ℝ) (hW : 0<W) (I : Finset ℕ)
    (hI : I⊆Finset.range (2*K+1)) :
    (∑ n∈I, ∫ z, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2 ∂planeMeasure)≤
      ∫ z, ‖f z‖^2 ∂planeMeasure := by
  have h := verticalBinLp_energy K W hW I hI (hf.toLp f)
  rw [memLp_toL2_norm_sq] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [verticalBinLp,verticalConvolutionLp_toLp _ _ _ f hfm hf,memLp_toL2_norm_sq]

end LipschitzHilbert.PacketRepresentation

end

end OAI
