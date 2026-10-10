import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeCommutation
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinReconstruction

namespace OAI

/-! Exact finite Schwartz input reconstruction through the short-time operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem slopeKernelOperator_schwartz_sum {ι : Type*} [Fintype ι]
    (K : ℝ → ℂ) (hK : Integrable K) (u : (ℝ×ℝ) → ℝ)
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator K u (show SchwartzMap (ℝ×ℝ) ℂ from ∑ n, f n) z=
      ∑ n, slopeKernelOperator K u (f n) z := by
  have hi (n : ι) : Integrable (fun t => K t*f n (z.1-t,z.2-t*u z)) := by
    apply (hK.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 (f n))).mono'
    · exact hK.aestronglyMeasurable.mul ((f n).continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ (f n) _) (norm_nonneg _)
  unfold slopeKernelOperator
  simp only [sum_apply,Finset.mul_sum]
  exact integral_finsetSum _ (fun n _ => hi n)

theorem shortSlopeOperator_schwartz_sum {ι : Type*} [Fintype ι]
    (K : ℝ → ℂ) (hK : Integrable K) (u : (ℝ×ℝ) → ℝ)
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    shortSlopeOperator K u (show SchwartzMap (ℝ×ℝ) ℂ from ∑ n, f n) z=
      ∑ n, shortSlopeOperator K u (f n) z := by
  simp only [shortSlopeOperator_eq_kernel]
  exact slopeKernelOperator_schwartz_sum _ (shortTimeKernel_integrable K hK) u f z

theorem shortSlopeOperator_bin_reconstruction (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (w W c C : ℝ) (hw : 0<w) (hW : 0<W) (hc : 0<c)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C)
    (z : ℝ×ℝ) :
    let J := ⌈C*W/w⌉₊
    let I := verticalBinLabels J w W c C
    shortSlopeOperator K u f z=
      ∑ n : I, shortSlopeOperator K u
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n)
          (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f)) z := by
  intro J I
  have hr := verticalBin_schwartz_reconstruction f w W c C hw hW hc hband
  have hr' : (∑ n : I, schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n)
      (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f))=f := by
    exact (Finset.sum_coe_sort I (fun n : ℕ =>
      schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n)
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f))).trans hr
  calc
    _ = shortSlopeOperator K u (show SchwartzMap (ℝ×ℝ) ℂ from
        ∑ n : I, schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n)
          (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f)) z :=
      congrArg (fun g : SchwartzMap (ℝ×ℝ) ℂ => shortSlopeOperator K u g z) hr'.symm
    _ = _ := shortSlopeOperator_schwartz_sum K hK u _ z

end LipschitzHilbert.PacketRepresentation

end

end OAI
