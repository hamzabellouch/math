import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabKernelEstimates
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Quadratic horizontal variation of a centered Coulomb line integral. -/

noncomputable section
namespace ContinuumCoulomb

theorem coulombLine_boundary_difference {A H x : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hx : |x| ≤ H/2) :
    |coulombLineKernel A (x+H)-coulombLineKernel A (x-H)| ≤ 16*|x|/H^2 := by
  have hlo : -(H/2) ≤ x := (abs_le.mp hx).1
  have hhi : x ≤ H/2 := (abs_le.mp hx).2
  have hp : (H/2)^2 ≤ (x+H)^2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr (by linarith)
  have hn : (H/2)^2 ≤ (H-x)^2 :=
    (sq_le_sq₀ (by positivity) (by linarith)).mpr (by linarith)
  have hb := reciprocal_sqrt_difference_bound (show 0 < H/2 by positivity)
    (show (H/2)^2 ≤ A+(x+H)^2 by linarith)
    (show (H/2)^2 ≤ A+(x-H)^2 by nlinarith)
  have he : (A+(x+H)^2)-(A+(x-H)^2) = 4*H*x := by ring
  rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4), abs_of_pos hH] at hb
  change |coulombLineKernel A (x+H)-coulombLineKernel A (x-H)| ≤ _ at hb
  convert hb using 1
  field_simp
  ring

theorem coulombLineIntegral_quadratic_variation {A H x : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hx : |x| ≤ H/2) :
    |centeredLineIntegral (coulombLineKernel A) H x-
      centeredLineIntegral (coulombLineKernel A) H 0| ≤ 16*x^2/H^2 := by
  let f := centeredLineIntegral (coulombLineKernel A) H
  let d := fun t => coulombLineKernel A (t+H)-coulombLineKernel A (t-H)
  have hd (t : ℝ) : HasDerivAt f (d t) t :=
    centeredLineIntegral_hasDerivAt _ (coulombLineKernel_continuous hA) H t
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (-|x|) |x|) : ‖d t‖ ≤ 16*|x|/H^2 := by
    have ht' : |t| ≤ |x| := abs_le.mpr ht
    have h := coulombLine_boundary_difference hA hH (ht'.trans hx)
    rw [Real.norm_eq_abs]
    exact h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht' (by norm_num)) (sq_nonneg H))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hbound (convex_Icc (-|x|) |x|)
    (show (0:ℝ) ∈ Set.Icc (-|x|) |x| by constructor <;> linarith [abs_nonneg x])
    (show x ∈ Set.Icc (-|x|) |x| from ⟨neg_abs_le x, le_abs_self x⟩)
  simpa only [Real.norm_eq_abs, sub_zero, f, div_mul_eq_mul_div, mul_assoc, ← pow_two, sq_abs] using h

end ContinuumCoulomb

end

end OAI
