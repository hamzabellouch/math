import OAI.Geometry.SurfaceImmersion.Correction.SmoothingKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution

namespace OAI

/-! The actual smoothing operators from the finite-moment kernels. They are
linear on locally integrable inputs, smooth their outputs, and fix constants. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

def kernel (r : ℕ) : Base → ℝ := Classical.choose (exists_smoothing_kernel r)

lemma kernel_smooth (r : ℕ) : ContDiff ℝ ∞ (kernel r) :=
  (Classical.choose_spec (exists_smoothing_kernel r)).1

lemma kernel_compact (r : ℕ) : HasCompactSupport (kernel r) :=
  (Classical.choose_spec (exists_smoothing_kernel r)).2.1

lemma kernel_mass (r : ℕ) : (∫ x, kernel r x) = 1 :=
  (Classical.choose_spec (exists_smoothing_kernel r)).2.2.1

lemma kernel_moment (r : ℕ) (α : Fin 2 → ℕ) (hα : 1 ≤ degree α) (hαr : degree α ≤ r) :
    (∫ x, monomial α x * kernel r x) = 0 :=
  (Classical.choose_spec (exists_smoothing_kernel r)).2.2.2 α hα hαr

lemma mass_dilate (K : Base → ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x, dilate K s x) = ∫ x, K x := by
  simpa only [monomial, degree, Finset.sum_const_zero, pow_zero,
    Finset.prod_const_one, one_mul] using moment_dilate K (fun _ => 0) hs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Smoothing at scale `s`, using the kernel whose moments vanish through `r`. -/
def smooth (r : ℕ) (s : ℝ) (f : Base → E) : Base → E :=
  (dilate (kernel r) s) ⋆[lsmul ℝ ℝ, volume] f

omit [CompleteSpace E] in
lemma smooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (smooth r s f) :=
  (compact_dilate (kernel_compact r) hs.ne').contDiff_convolution_left (lsmul ℝ ℝ)
    (smooth_dilate (kernel_smooth r) s) hf

omit [CompleteSpace E] in
lemma smooth_add (r : ℕ) {s : ℝ} (hs : 0 < s) {f g : Base → E}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    smooth r s (f + g) = smooth r s f + smooth r s g := by
  have hc := compact_dilate (kernel_compact r) hs.ne'
  have hcont := (smooth_dilate (kernel_smooth r) s).continuous
  exact (hc.convolutionExists_left (lsmul ℝ ℝ) hcont hf).distrib_add
    (hc.convolutionExists_left (lsmul ℝ ℝ) hcont hg)

omit [CompleteSpace E] in
lemma smooth_smul (r : ℕ) (s a : ℝ) (f : Base → E) :
    smooth r s (a • f) = a • smooth r s f :=
  convolution_smul

lemma smooth_const (r : ℕ) {s : ℝ} (hs : 0 < s) (v : E) :
    smooth r s (fun _ => v) = fun _ => v := by
  funext x
  change (∫ y, dilate (kernel r) s y • v) = v
  rw [integral_smul_const, mass_dilate (kernel r) hs, kernel_mass, one_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
