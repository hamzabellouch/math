import Mathlib.Analysis.Calculus.SmoothSeries

namespace OAI

noncomputable section

namespace Problem340

open Set
open scoped ContDiff

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ι → E → F} {u : ι → ℝ} {s : Set E} {x₀ : E}

theorem hasFDerivAt_tsum_on_chart
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) s)
    (hu : Summable u)
    (hbound : ∀ i x, x ∈ s → ‖fderiv ℝ (f i) x‖ ≤ u i)
    (hx₀ : x₀ ∈ s) (hbase : Summable (fun i => f i x₀))
    {x : E} (hx : x ∈ s) :
    HasFDerivAt (fun y => ∑' i, f i y)
      (∑' i, fderiv ℝ (f i) x) x := by
  apply hasFDerivAt_tsum_of_isPreconnected hu hs hconn
    (fun i y hy => ?_) hbound hx₀ hbase hx
  exact ((hf i).differentiableOn_one y hy).differentiableAt
    (hs.mem_nhds hy) |>.hasFDerivAt

theorem contDiffOn_tsum_on_chart
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) s)
    (hu : Summable u)
    (hbound : ∀ i x, x ∈ s → ‖fderiv ℝ (f i) x‖ ≤ u i)
    (hx₀ : x₀ ∈ s) (hbase : Summable (fun i => f i x₀)) :
    ContDiffOn ℝ 1 (fun x => ∑' i, f i x) s := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn]
  refine ⟨by simp, (fun x => ∑' i, fderiv ℝ (f i) x), ?_, ?_⟩
  · apply contDiffOn_zero.mpr
    exact continuousOn_tsum
      (fun i => (hf i).continuousOn_fderiv_of_isOpen hs (by rfl)) hu hbound
  · intro x hx
    exact (hasFDerivAt_tsum_on_chart hs hconn hf hu hbound hx₀ hbase hx).hasFDerivWithinAt

theorem hasFDerivAt_tsum_on_open
    (hs : IsOpen s) (hf : ∀ i, ContDiffOn ℝ 1 (f i) s)
    (hu : Summable u)
    (hbound : ∀ i x, x ∈ s → ‖fderiv ℝ (f i) x‖ ≤ u i)
    (hpoint : ∀ x ∈ s, Summable (fun i => f i x))
    {x : E} (hx : x ∈ s) :
    HasFDerivAt (fun y => ∑' i, f i y)
      (∑' i, fderiv ℝ (f i) x) x := by
  classical
  apply hasFDerivAt_of_tendstoUniformlyOn hs (tendstoUniformlyOn_tsum hu hbound)
    (fun t y hy => ?_) (fun y hy => (hpoint y hy).hasSum) hx
  exact HasFDerivAt.fun_sum fun i _ =>
    ((hf i).differentiableOn_one y hy).differentiableAt
      (hs.mem_nhds hy) |>.hasFDerivAt

theorem contDiffOn_tsum_on_open
    (hs : IsOpen s) (hf : ∀ i, ContDiffOn ℝ 1 (f i) s)
    (hu : Summable u)
    (hbound : ∀ i x, x ∈ s → ‖fderiv ℝ (f i) x‖ ≤ u i)
    (hpoint : ∀ x ∈ s, Summable (fun i => f i x)) :
    ContDiffOn ℝ 1 (fun x => ∑' i, f i x) s := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn]
  refine ⟨by simp, (fun x => ∑' i, fderiv ℝ (f i) x), ?_, ?_⟩
  · apply contDiffOn_zero.mpr
    exact continuousOn_tsum
      (fun i => (hf i).continuousOn_fderiv_of_isOpen hs (by rfl)) hu hbound
  · intro x hx
    exact (hasFDerivAt_tsum_on_open hs hf hu hbound hpoint hx).hasFDerivWithinAt

theorem contDiffOn_tsum_of_norm_add_fderiv_bound
    (hs : IsOpen s) (hf : ∀ i, ContDiffOn ℝ 1 (f i) s)
    (hu : Summable u)
    (hbound : ∀ i x, x ∈ s → ‖f i x‖ + ‖fderiv ℝ (f i) x‖ ≤ u i) :
    ContDiffOn ℝ 1 (fun x => ∑' i, f i x) s := by
  apply contDiffOn_tsum_on_open hs hf hu
  · intro i x hx
    exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hbound i x hx)
  · intro x hx
    exact Summable.of_norm_bounded hu fun i =>
      le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hbound i x hx)

end Problem340

end

end OAI
