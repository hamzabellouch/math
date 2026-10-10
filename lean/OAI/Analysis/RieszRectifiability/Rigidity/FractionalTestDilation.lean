import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel
import OAI.Analysis.RieszRectifiability.Kernel.ExteriorDilation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def dilatedFractionalKernel {d : ℕ} (m : ℕ) (g : Ambient d → F)
    (x : Ambient d) (t : ℝ) (h : Ambient d) : F :=
  inverseDistancePow (m + 1) 0 h • symmetricSecondDifference g x (t • h)

def dilatedFractionalGradientKernel {d : ℕ} (m : ℕ) (g : Ambient d → F)
    (x : Ambient d) (t : ℝ) (h : Ambient d) : F :=
  inverseDistancePow (m + 1) 0 h •
    (fderiv ℝ g (x + t • h) h - fderiv ℝ g (x - t • h) h)

theorem dilatedFractionalKernel_scaling {d : ℕ} (m : ℕ) (g : Ambient d → F)
    (x : Ambient d) (t : ℝ) (ht : 0 < t) (h : Ambient d) :
    dilatedFractionalKernel m g x t h =
      t ^ (m + 1) • fractionalSchwartzKernel m g x (t • h) := by
  unfold dilatedFractionalKernel fractionalSchwartzKernel
  rw [inverseDistancePow_origin_smul (m + 1) t ht, smul_smul]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]

theorem dilatedFractionalKernel_integral_scaling (n : ℕ) (g : Ambient n → F)
    (x : Ambient n) (t : ℝ) (ht : 0 < t) :
    (∫ h, dilatedFractionalKernel n g x t h) = t • ∫ h, fractionalSchwartzKernel n g x h := by
  have heq : dilatedFractionalKernel n g x t =
      fun h => t ^ (n + 1) • fractionalSchwartzKernel n g x (t • h) :=
    funext (dilatedFractionalKernel_scaling n g x t ht)
  rw [heq, integral_smul,
    Measure.integral_comp_smul_of_nonneg (volume : Measure (Ambient n))
      (fractionalSchwartzKernel n g x) t (hR := ht.le), smul_smul]
  congr 1
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, pow_succ]
  field_simp

theorem dilatedFractionalKernel_hasDerivAt {d : ℕ} (m : ℕ)
    (g : Ambient d → F) (hg : Differentiable ℝ g) (x h : Ambient d) (t : ℝ) :
    HasDerivAt (fun r => dilatedFractionalKernel m g x r h)
      (dilatedFractionalGradientKernel m g x t h) t := by
  have hp : HasDerivAt (fun r : ℝ => g (x + r • h)) (fderiv ℝ g (x + t • h) h) t := by
    simpa only [zero_add, one_smul] using!
      (hg (x + t • h)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const h))
  have hm : HasDerivAt (fun r : ℝ => g (x - r • h)) (-fderiv ℝ g (x - t • h) h) t := by
    simpa only [zero_sub, one_smul, map_neg] using!
      (hg (x - t • h)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).sub ((hasDerivAt_id t).smul_const h))
  have hdiff := ((hp.add hm).sub (hasDerivAt_const t ((2 : ℝ) • g x))).const_smul
    (inverseDistancePow (m + 1) 0 h)
  simpa only [dilatedFractionalKernel, dilatedFractionalGradientKernel,
    symmetricSecondDifference, Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
    sub_zero, sub_eq_add_neg, neg_zero, add_zero] using! hdiff

end

end RieszRectifiability

end OAI
