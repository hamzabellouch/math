import OAI.Analysis.LipschitzHilbert.Fourier.HilbertFiniteSymbol
import OAI.Analysis.LipschitzHilbert.Fourier.LineProjectionKernel

namespace OAI

/-! Uniform L2 bounds for the actual finite smooth Hilbert convolutions. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_unit (q : SchwartzMap ℝ ℂ) :
    lineProjectionKernel q 1 (by norm_num)=𝓕⁻ q := by
  unfold lineProjectionKernel
  congr 1
  ext x
  simp only [dilatedSlopeWindow_apply,one_mul]

theorem hilbertFinite_kernel (N : ℕ) (L : ℝ) (hL : 0<L) (x : ℝ) :
    lineProjectionKernel (hilbertFiniteSymbol N L hL) 1 (by norm_num) x=
      finiteTimeKernel hilbertTimeKernel N L x := by
  have he : lineProjectionKernel (hilbertFiniteSymbol N L hL) 1 (by norm_num)=
      ∑ j : Fin N, lineProjectionKernel hilbertAnnularSymbol (L/(2:ℝ)^j.val)
        (ne_of_gt (div_pos hL (pow_pos (by norm_num) j.val))) := by
    rw [lineProjectionKernel_unit,hilbertFiniteSymbol,FourierTransform.fourierInv_sum]
    rfl
  rw [he]
  simp only [sum_apply,finiteTimeKernel]
  apply Finset.sum_congr rfl
  intro j _
  rw [lineProjectionKernel_eq_scaled _ _ (div_pos hL (pow_pos (by norm_num) j.val)),
    scaledSchwartzKernel_apply]
  rfl

theorem hilbertFinite_L2 (N : ℕ) (L : ℝ) (hL : 0<L) (f : SchwartzMap ℝ ℂ) :
    MemLp (lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f) 2 volume ∧
      (∫ x, ‖lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f x‖^2)≤
        Real.pi^2*(∫ x, ‖f x‖^2) := by
  have he : lineConvolution (finiteTimeKernel hilbertTimeKernel N L) f=
      lineSchwartzProjection (hilbertFiniteSymbol N L hL) 1 (by norm_num) f := by
    funext x
    rw [lineSchwartzProjection_eq_convolution]
    simp only [lineConvolution,hilbertFinite_kernel]
  rw [he]
  exact ⟨(lineSchwartzProjection _ _ _ f).memLp 2 volume,
    lineSchwartzProjection_energy _ 1 (by norm_num) Real.pi (hilbertFiniteSymbol_norm N L hL) f⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
