import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace OAI

/-! # Orthogonal centering of Hilbert-valued square-integrable functions

The mean is the closest constant in L2. This is the variance estimate used
after conditioning on the middle and right independent random-walk blocks.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X K : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def hilbertConstantL2 (μ : Measure X) [IsProbabilityMeasure μ] (v : K) : Lp K 2 μ :=
  (memLp_const v).toLp (fun _ => v)

omit [InnerProductSpace ℂ K] in
theorem hilbertConstantL2_ae (v : K) :
    hilbertConstantL2 μ v =ᵐ[μ] fun _ => v := MemLp.coeFn_toLp _

variable [CompleteSpace K]

theorem integral_hilbertConstantL2 (v : K) : ∫ x, hilbertConstantL2 μ v x ∂μ = v := by
  rw [integral_congr_ae (hilbertConstantL2_ae v)]
  simp

theorem inner_hilbertConstantL2_left (v : K) (f : Lp K 2 μ) :
    inner ℂ (hilbertConstantL2 μ v) f = inner ℂ v (∫ x, f x ∂μ) := by
  rw [L2.inner_def]
  calc
    (∫ x, inner ℂ (hilbertConstantL2 μ v x) (f x) ∂μ) = ∫ x, inner ℂ v (f x) ∂μ :=
      integral_congr_ae ((hilbertConstantL2_ae v).mono (fun _ hx => by
        dsimp only at hx ⊢
        rw [hx]))
    _ = _ := integral_inner ((Lp.memLp f).integrable (by norm_num)) v

theorem hilbertL2_centered_orthogonal (f : Lp K 2 μ) (v : K) :
    inner ℂ (hilbertConstantL2 μ v) (f - hilbertConstantL2 μ (∫ x, f x ∂μ)) = 0 := by
  rw [inner_sub_right, inner_hilbertConstantL2_left, inner_hilbertConstantL2_left,
    integral_hilbertConstantL2, sub_self]

theorem hilbertL2_variance_identity (f : Lp K 2 μ) (v : K) :
    ‖f - hilbertConstantL2 μ v‖ ^ 2 =
      ‖f - hilbertConstantL2 μ (∫ x, f x ∂μ)‖ ^ 2 +
      ‖hilbertConstantL2 μ (∫ x, f x ∂μ) - hilbertConstantL2 μ v‖ ^ 2 := by
  let a := hilbertConstantL2 μ (∫ x, f x ∂μ)
  let b := hilbertConstantL2 μ v
  have hi : inner ℂ (f - a) (a - b) = 0 := by
    rw [inner_sub_right]
    have h₁ : inner ℂ (f - a) a = 0 := inner_eq_zero_symm.mp (hilbertL2_centered_orthogonal f _)
    have h₂ : inner ℂ (f - a) b = 0 := inner_eq_zero_symm.mp (hilbertL2_centered_orthogonal f v)
    rw [h₁, h₂, sub_self]
  have he : f - b = (f - a) + (a - b) := by abel
  change ‖f - b‖ ^ 2 = ‖f - a‖ ^ 2 + ‖a - b‖ ^ 2
  rw [he]
  simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi

theorem hilbertL2_centering_minimizes (f : Lp K 2 μ) (v : K) :
    ‖f - hilbertConstantL2 μ (∫ x, f x ∂μ)‖ ≤ ‖f - hilbertConstantL2 μ v‖ := by
  have hv := hilbertL2_variance_identity f v
  nlinarith [sq_nonneg ‖hilbertConstantL2 μ (∫ x, f x ∂μ) - hilbertConstantL2 μ v‖,
    norm_nonneg (f - hilbertConstantL2 μ (∫ x, f x ∂μ)), norm_nonneg (f - hilbertConstantL2 μ v)]

end

end KadisonKastler

end OAI
