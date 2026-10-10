import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.BoundedDegreeMonomials

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]

omit [FiniteDimensional ℝ E] in
lemma finiteTaylorFunction_three (f : E → ℝ) (x : E) :
    finiteTaylorFunction f 3 x = f 0 + fderiv ℝ f 0 x +
      (2 : ℝ)⁻¹ * iteratedFDeriv ℝ 2 f 0 (fun _ => x) := by
  simp [finiteTaylorFunction, Finset.sum_range_succ, iteratedFDeriv_one_apply,
    Nat.factorial, smul_eq_mul]

theorem compact_uniform_negative_hessian_localization
    (f : X → E → ℝ) (hf : ∀ p, ContDiff ℝ ∞ (f p))
    (hthird : Continuous (fun q : X × E => iteratedFDeriv ℝ 3
      (fun y => f q.1 y - finiteTaylorFunction (f q.1) 3 y) q.2))
    {K : Set X} (hK : IsCompact K) (δ : X → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ p ∈ K, ∀ x, fderiv ℝ (f p) 0 x ≤ δ p * ‖x‖)
    (hquadratic : ∀ p ∈ K, ∀ x,
      iteratedFDeriv ℝ 2 (f p) 0 (fun _ => x) ≤ -4 * κ * ‖x‖ ^ 2) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ K, ∀ x ∈ Metric.ball (0 : E) r,
      f p x ≤ f p 0 + δ p * ‖x‖ - κ * ‖x‖ ^ 2 := by
  obtain ⟨C₀,hC₀⟩ := (hK.prod (isCompact_closedBall (0 : E) 1)).exists_bound_of_continuousOn
    hthird.continuousOn
  let C := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨min 1 (κ / C), lt_min zero_lt_one (div_pos hκ hC), ?_⟩
  intro p hp x hx
  have hbound := vanishing_jet_norm_bound
    (fun y => f p y - finiteTaylorFunction (f p) 3 y)
    ((hf p).sub (contDiff_finiteTaylorFunction (f p) 3)) 3 1 C hC.le
    (fun k hk => finiteTaylorFunction_remainder_jet (hf p) 3 k hk)
    (fun y hy => (hC₀ (p,y) ⟨hp,Metric.ball_subset_closedBall hy⟩).trans (le_max_left _ _))
  have hxnorm : ‖x‖ < min 1 (κ / C) := by simpa using hx
  have hxball : x ∈ Metric.ball (0 : E) 1 := by
    simpa using hxnorm.trans_le (min_le_left _ _)
  have hxsmall : C * ‖x‖ ≤ κ := by
    have h := (lt_div_iff₀ hC).mp (hxnorm.trans_le (min_le_right _ _))
    nlinarith
  have herr := hbound 3 (le_refl _) x hxball
  change ‖iteratedFDeriv ℝ 0 (fun y => f p y - finiteTaylorFunction (f p) 3 y) x‖ ≤
    C * ‖x‖ ^ 3 at herr
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at herr
  have hu : f p x - finiteTaylorFunction (f p) 3 x ≤ C * ‖x‖ ^ 3 :=
    (le_abs_self _).trans herr
  rw [finiteTaylorFunction_three] at hu
  have hq := hquadratic p hp x
  have hl := hlinear p hp x
  have hrem : C * ‖x‖ ^ 3 ≤ κ * ‖x‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hxsmall (sq_nonneg ‖x‖)
    nlinarith
  norm_num at hu
  linarith
end YauCounterexamples

end

end OAI
