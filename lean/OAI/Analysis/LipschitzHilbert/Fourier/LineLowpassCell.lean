import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelMaximal
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineNesting

namespace OAI

/-! Uniform cellwise bounds for a smooth projection at any fixed ratio
between its physical scale and the cell length. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def lineCellMaximalConstant (q : SchwartzMap ℝ ℂ) (ratio : ℝ) : ℝ :=
  60*lineKernelDecayConstant q*(1+1/ratio)

theorem lineCellMaximalConstant_nonneg (q : SchwartzMap ℝ ℂ) (ratio : ℝ) (hratio : 0<ratio) :
    0≤lineCellMaximalConstant q ratio :=
  mul_nonneg (mul_nonneg (by norm_num) (lineKernelDecayConstant_nonneg q)) (by positivity)

theorem cell_abs_sub_le (q k i : ℤ) {x y : ℝ}
    (hx : x∈cell q k i) (hy : y∈cell q k i) : |x-y|≤scale k := by
  have hwidth : left q k (i+1)-left q k i=scale k := by
    unfold left
    push_cast
    ring
  exact abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩

theorem lineProjection_cell_maximal (q : SchwartzMap ℝ ℂ) (ratio : ℝ) (hratio : 0<ratio)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hfb : ∀ x, ‖f x‖≤B) :
    ∀ᵐ y ∂volume, ∀ grid k i : ℤ, y∈cell grid k i → ∀ x∈cell grid k i,
      ‖lineConvolution (lineProjectionKernel q (ratio*scale k) (mul_pos hratio (scale_pos k)).ne') f x‖≤
        lineCellMaximalConstant q ratio*threeGridMaximal (fun z => ‖f z‖) y := by
  filter_upwards [lineProjectionKernel_maximal q f hfm hf B hfb] with y hy
  intro grid k i hycell x hxcell
  have h := hy (ratio*scale k) (scale k) x (mul_pos hratio (scale_pos k)) (scale_pos k).le
    (cell_abs_sub_le grid k i hxcell hycell)
  have he : scale k/(ratio*scale k)=1/ratio := by field_simp [(scale_pos k).ne']
  simpa only [he,lineCellMaximalConstant] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
