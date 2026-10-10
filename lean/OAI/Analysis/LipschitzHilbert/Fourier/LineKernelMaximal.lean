import OAI.Analysis.LipschitzHilbert.Fourier.KernelAverageBound
import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelDecay
import OAI.Analysis.LipschitzHilbert.Trees.SourceThreeGridMaximal

namespace OAI

/-! The actual low-pass convolution is dominated, uniformly over centers
in a cell, by the existing three-grid maximal function. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem integral_reflected_interval (f : ℝ → ℝ) (x r : ℝ) :
    (∫ t in Icc (-r) r, f (x-t))=∫ z in Icc (x-r) (x+r), f z := by
  rw [←integral_indicator measurableSet_Icc,←integral_indicator measurableSet_Icc]
  have h := integral_sub_left_eq_self ((Icc (x-r) (x+r)).indicator f) volume x
  rw [←h]
  apply integral_congr_ae
  filter_upwards [] with t
  have he : (x-t∈Icc (x-r) (x+r))↔t∈Icc (-r) r := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  by_cases ht : t∈Icc (-r) r
  · simp only [indicator_of_mem ht,indicator_of_mem (he.mpr ht)]
  · simp only [indicator_of_notMem ht,indicator_of_notMem (mt he.mp ht)]

theorem lineProjectionKernel_maximal (q : SchwartzMap ℝ ℂ)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hfb : ∀ x, ‖f x‖≤B) :
    ∀ᵐ y ∂volume, ∀ W L x : ℝ, ∀ (hW : 0<W), 0≤L → |x-y|≤L →
      ‖lineConvolution (lineProjectionKernel q W hW.ne') f x‖≤
        60*lineKernelDecayConstant q*(1+L/W)*threeGridMaximal (fun z => ‖f z‖) y := by
  have hmax := interval_average_le_threeGridMaximal hf.norm (fun _ => norm_nonneg _)
  filter_upwards [hmax] with y hy
  intro W L x hW hL hxy
  let M := threeGridMaximal (fun z => ‖f z‖) y
  have hM : 0≤M := threeGridMaximal_nonneg _ _
  have hR : 0<W+L := by linarith
  have hmean (r : ℝ) (hr : W+L≤r) : (∫ t in Icc (-r) r, ‖f (x-t)‖)≤12*r*M := by
    rw [integral_reflected_interval (fun z => ‖f z‖) x r]
    have hrr : 0<r := hR.trans_le hr
    have hyI : y∈Icc (x-r) (x+r) := by
      obtain ⟨h1,h2⟩ := abs_le.mp hxy
      exact ⟨by linarith,by linarith⟩
    have h := hy x r hrr hyI
    exact (div_le_iff₀ (by positivity : 0<2*r)).mp h |>.trans_eq (by dsimp [M]; ring)
  have hk := kernel_average_bound (lineProjectionKernel q W hW.ne') f
    (lineProjectionKernel q W hW.ne').integrable hfm B hfb
    (lineKernelDecayConstant q/W) (lineKernelDecayConstant q*W) (W+L) M x
    (div_nonneg (lineKernelDecayConstant_nonneg q) hW.le)
    (mul_nonneg (lineKernelDecayConstant_nonneg q) hW.le) hR hM
    (fun t => (lineProjectionKernel_decay q W hW t).1)
    (fun t => (lineProjectionKernel_decay q W hW t).2) hmean
  apply hk.trans
  have hratio : W/(W+L)≤(W+L)/W := by
    apply (div_le_div_iff₀ hR hW).mpr
    nlinarith
  calc
    _ = 12*lineKernelDecayConstant q*((W+L)/W)*M+
        48*lineKernelDecayConstant q*(W/(W+L))*M := by ring
    _ ≤ 12*lineKernelDecayConstant q*((W+L)/W)*M+
        48*lineKernelDecayConstant q*((W+L)/W)*M := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) (lineKernelDecayConstant_nonneg q))) hM)
    _ = _ := by field_simp; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
