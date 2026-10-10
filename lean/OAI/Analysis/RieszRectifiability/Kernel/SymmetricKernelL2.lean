import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellEnergy

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Function Set

variable {X : Type*} [MeasurableSpace X]

theorem row_weighted_square_integrable_and_bound
    (μ : Measure X) [IsFiniteMeasure μ] (k : X × X → ℝ)
    (hk : Measurable k) (hk0 : ∀ q, 0 ≤ k q)
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (B : ℝ) (hB : ∀ x, (∫ y, k (x, y) ∂μ) ≤ B)
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ) :
    Integrable (fun q : X × X => w q.1 ^ 2 * k q) (μ.prod μ) ∧
      (∫ q : X × X, w q.1 ^ 2 * k q ∂μ.prod μ) ≤ B * (∫ x, w x ^ 2 ∂μ) := by
  have hm : AEStronglyMeasurable (fun q : X × X => w q.1 ^ 2 * k q) (μ.prod μ) := by
    fun_prop
  have hi : Integrable (fun q : X × X => w q.1 ^ 2 * k q) (μ.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨Filter.Eventually.of_forall (fun x => (hrow x).const_mul (w x ^ 2)), ?_⟩
    apply (hL2.integrable_sq.const_mul B).mono' hm.norm.integral_prod_right'
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp_rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hk0 _)), integral_const_mul]
    simpa only [mul_comm B] using! mul_le_mul_of_nonneg_left (hB x) (sq_nonneg (w x))
  refine ⟨hi, ?_⟩
  have houter := hi.integral_prod_left
  simp only [integral_const_mul] at houter
  rw [integral_prod _ hi]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∫ x, B * w x ^ 2 ∂μ :=
      integral_mono houter (hL2.integrable_sq.const_mul B) (fun x => by
        simpa only [mul_comm B] using! mul_le_mul_of_nonneg_left (hB x) (sq_nonneg (w x)))
    _ = _ := integral_const_mul _ _

theorem symmetric_weight_product_integrable_and_bound
    (μ : Measure X) [IsFiniteMeasure μ] (k : X × X → ℝ)
    (hk : Measurable k) (hk0 : ∀ q, 0 ≤ k q)
    (hsymm : ∀ x y, k (y, x) = k (x, y))
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (B : ℝ) (hB : ∀ x, (∫ y, k (x, y) ∂μ) ≤ B)
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ) :
    Integrable (fun q : X × X => |w q.1 * w q.2| * k q) (μ.prod μ) ∧
      (∫ q : X × X, |w q.1 * w q.2| * k q ∂μ.prod μ) ≤
        B * (∫ x, w x ^ 2 ∂μ) := by
  obtain ⟨hi₁, hb₁⟩ := row_weighted_square_integrable_and_bound μ k hk hk0 hrow B hB w hw hL2
  have hswap (q : X × X) : k q.swap = k q := hsymm q.1 q.2
  have hi₂ : Integrable (fun q : X × X => w q.2 ^ 2 * k q) (μ.prod μ) := by
    simpa only [Function.comp_def, Prod.fst_swap, hswap] using! hi₁.swap
  have heq : (∫ q : X × X, w q.2 ^ 2 * k q ∂μ.prod μ) =
      ∫ q : X × X, w q.1 ^ 2 * k q ∂μ.prod μ := by
    simpa only [Prod.fst_swap, hswap] using!
      (integral_prod_swap (μ := μ) (ν := μ) (fun q : X × X => w q.1 ^ 2 * k q))
  have hpoint (q : X × X) : |w q.1 * w q.2| * k q ≤
      (w q.1 ^ 2 * k q + w q.2 ^ 2 * k q) / 2 := by
    have h : 2 * |w q.1 * w q.2| ≤ w q.1 ^ 2 + w q.2 ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|w q.1| - |w q.2|), sq_abs (w q.1), sq_abs (w q.2)]
    have := mul_le_mul_of_nonneg_right h (hk0 q)
    nlinarith
  have hi : Integrable (fun q : X × X => |w q.1 * w q.2| * k q) (μ.prod μ) := by
    apply ((hi₁.add hi₂).div_const 2).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun q => by
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hk0 q))]
      exact hpoint q)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ q : X × X, (w q.1 ^ 2 * k q + w q.2 ^ 2 * k q) / 2 ∂μ.prod μ :=
      integral_mono hi ((hi₁.add hi₂).div_const 2) hpoint
    _ = ∫ q : X × X, w q.1 ^ 2 * k q ∂μ.prod μ := by
      rw [integral_div, integral_add hi₁ hi₂, heq]
      ring
    _ ≤ _ := hb₁

end

end RieszRectifiability

end OAI
