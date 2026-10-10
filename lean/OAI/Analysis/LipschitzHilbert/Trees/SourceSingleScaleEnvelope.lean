import OAI.Analysis.LipschitzHilbert.Fourier.LatticeCoefficientConvolution
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlopeLabels

namespace OAI

/-! The single-scale estimate in §5, `conc:original-positive`.
The lattice estimate is summed at the source point before integrating.
Only pointwise overlap of the label multipliers appears, so the estimate
has no factor counting the available labels. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planarPositiveConvolution_sum {Λ : Type*} [Fintype Λ]
    (f : Λ → ℝ×ℝ → ℝ) (hf : ∀ b, Measurable (f b))
    {l W B : ℝ} (hl : 0 < l) (hW : 0 < W)
    (hbound : ∀ b z, ‖f b z‖ ≤ B) (x y : ℝ) :
    planarPositiveConvolution l W (fun z => ∑ b, f b z) x y =
      ∑ b, planarPositiveConvolution l W (f b) x y := by
  unfold planarPositiveConvolution
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun b _ =>
    planarPositiveConvolution_integrable l W (f b) (hf b) hl hW (hbound b) x y)

theorem planarPositiveConvolution_le {l W B : ℝ} (hl : 0 < l) (hW : 0 < W)
    (hB : 0 ≤ B) (f : ℝ×ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) (hbound : ∀ z, f z ≤ B) (x y : ℝ) :
    planarPositiveConvolution l W f x y ≤ B*Real.pi^2 := by
  have hb (z : ℝ×ℝ) : ‖f z‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 z)]
    exact hbound z
  have hx : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  have hy : Integrable (fun s => lineKernel W (y-s)) := by
    simp_rw [lineKernel_sub_comm W y]
    exact lineKernel_integrable W y hW
  have hkernel : (∫ z : ℝ×ℝ, lineKernel l (x-z.1)*lineKernel W (y-z.2)) ≤ Real.pi^2 := by
    rw [Measure.volume_eq_prod,integral_prod_mul (fun s : ℝ => lineKernel l (x-s))
      (fun s : ℝ => lineKernel W (y-s))]
    have hxle : (∫ s, lineKernel l (x-s)) ≤ Real.pi := by
      simpa only [lineKernel_sub_comm l x] using integral_lineKernel_le l x hl
    have hyle : (∫ s, lineKernel W (y-s)) ≤ Real.pi := by
      simpa only [lineKernel_sub_comm W y] using integral_lineKernel_le W y hW
    have hyn : 0 ≤ ∫ s, lineKernel W (y-s) := integral_nonneg (fun _ => lineKernel_nonneg _ _ hW)
    simpa only [pow_two] using mul_le_mul hxle hyle hyn Real.pi_pos.le
  calc
    _ ≤ ∫ z : ℝ×ℝ, (lineKernel l (x-z.1)*lineKernel W (y-z.2))*B := by
      apply integral_mono (planarPositiveConvolution_integrable l W f hf hl hW hb x y)
        ((hx.mul_prod hy).mul_const B)
      intro z
      exact mul_le_mul_of_nonneg_left (hbound z)
        (mul_nonneg (lineKernel_nonneg _ _ hl) (lineKernel_nonneg _ _ hW))
    _ = B*(∫ z : ℝ×ℝ, lineKernel l (x-z.1)*lineKernel W (y-z.2)) := by
      rw [integral_mul_const,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hkernel hB

theorem sum_planarPositiveConvolution_le {Λ : Type*} [Fintype Λ]
    (f : Λ → ℝ×ℝ → ℝ) (hf : ∀ b, Measurable (f b))
    (hf0 : ∀ b z, 0 ≤ f b z) {l W B : ℝ}
    (hl : 0 < l) (hW : 0 < W) (hB : 0 ≤ B)
    (hoverlap : ∀ z, ∑ b, f b z ≤ B) (x y : ℝ) :
    (∑ b, planarPositiveConvolution l W (f b) x y) ≤ B*Real.pi^2 := by
  have hb (b : Λ) (z : ℝ×ℝ) : ‖f b z‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 b z)]
    exact (Finset.single_le_sum (fun c _ => hf0 c z) (Finset.mem_univ b)).trans (hoverlap z)
  rw [← planarPositiveConvolution_sum f hf hl hW hb x y]
  exact planarPositiveConvolution_le hl hW hB _
    (Finset.measurable_sum _ (fun b _ => hf b))
    (fun z => Finset.sum_nonneg (fun b _ => hf0 b z)) hoverlap x y

/-- Each label may have its own translated lattice. They share the
physical scale, transverse width, source test, and pointwise overlap
budget. All analyzing coefficients are the actual integral coefficients. -/
theorem source_single_scale_envelope {Λ κ : Type*} [Fintype Λ] [Fintype κ]
    (ι : Λ → Type*) [∀ b, Fintype (ι b)]
    (site : ∀ b, ι b → ℤ×ℤ) (hinj : ∀ b, Function.Injective (site b))
    (originX originY : Λ → ℝ) {l W B : ℝ} (hl : 0 < l) (hW : 0 < W) (hB : 0 ≤ B)
    (source : Λ → ℝ×ℝ → ℝ) (hmeas : ∀ b, Measurable (source b))
    (hnonneg : ∀ b z, 0 ≤ source b z) (hoverlap : ∀ z, ∑ b, source b z ≤ B)
    (wave : ∀ b, ι b → κ → ℝ×ℝ → ℂ) (hwave : ∀ b i k, Measurable (wave b i k))
    (hbound : ∀ b i k z, ‖wave b i k z‖ ≤
      tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z*source b z)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ×ℝ) :
    (∑ b, ∑ i, ‖analyzingCoefficient volume (fun _ : ι b => l*W) (wave b) g i‖*
      tileEnvelope (originX b+l*(site b i).1) (originY b+W*(site b i).2) l W 6 z) ≤
        (64*(4*Real.pi)^2)*(B*Real.pi^2) := by
  have hb (b : Λ) (p : ℝ×ℝ) : ‖source b p‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hnonneg b p)]
    exact (Finset.single_le_sum (fun c _ => hnonneg c p) (Finset.mem_univ b)).trans (hoverlap p)
  calc
    _ ≤ ∑ b, (64*(4*Real.pi)^2)*planarPositiveConvolution l W (source b) z.1 z.2 := by
      apply Finset.sum_le_sum
      intro b _
      exact lattice_coefficient_convolution (site b) (hinj b) (originX b) (originY b) l W
        hl hW (source b) (hmeas b) (hnonneg b) (hb b) (wave b) (hwave b) (hbound b) g hg hg1 z
    _ = (64*(4*Real.pi)^2)*∑ b, planarPositiveConvolution l W (source b) z.1 z.2 :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_planarPositiveConvolution_le source hmeas hnonneg hl hW hB hoverlap z.1 z.2)
      (by positivity)

end LipschitzHilbert

end

end OAI
