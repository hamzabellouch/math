import OAI.Analysis.CircleDomains.Selection.PriorityFinite

namespace OAI

/-! The countable horizontal interpolation has the finite derivative
bound at every point where the tail cutoffs vanish on a neighborhood. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem priorityList_derivative_cost (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (N : ℕ) (p : E) :
    ((priorityList χ c N).map (fun e => ‖fderiv ℝ e.1 p‖)).sum =
      ∑ n ∈ Finset.range N, ‖fderiv ℝ (χ n) p‖ := by
  induction N with
  | zero => simp [priorityList]
  | succ N ih => simp only [priorityList_succ, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      ih, Finset.sum_range_succ]

 theorem priorityInfiniteValue_local_derivative
    (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) {p : E} {B : ℝ}
    (hX : DifferentiableAt ℝ X p) (hXb : ‖X p‖ ≤ B)
    (hχ : ∀ n, DifferentiableAt ℝ (χ n) p ∧ χ n p ∈ Icc (0 : ℝ) 1)
    (hc : ∀ n, ‖c n‖ ≤ B)
    (hs : Summable (fun n => ‖fderiv ℝ (χ n) p‖))
    (hz : ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n, N ≤ n → χ n q = 0) :
    DifferentiableAt ℝ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p ∧
    ‖fderiv ℝ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p-
        (1-∑' n, priorityWeight (fun j => χ j p) n) • fderiv ℝ X p‖ ≤
      2*B*(∑' n, ‖fderiv ℝ (χ n) p‖) := by
  obtain ⟨N, hz⟩ := hz
  have hpz : ∀ n, N ≤ n → χ n p = 0 := mem_of_mem_nhds hz
  have hlocal : (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) =ᶠ[𝓝 p]
      priorityBlend (priorityList χ c N) X := by
    filter_upwards [hz] with q hq
    exact priorityInfiniteValue_eq_finite c X hq
  have hL (e) (he : e ∈ priorityList χ c N) :
      DifferentiableAt ℝ e.1 p ∧ e.1 p ∈ Icc (0 : ℝ) 1 ∧ ‖e.2‖ ≤ B := by
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
    exact ⟨(hχ n).1, (hχ n).2, hc n⟩
  have hfd := priorityBlend_differentiableAt hX (fun e he => (hL e he).1)
  refine ⟨hfd.congr_of_eventuallyEq hlocal, ?_⟩
  have hcoef : 1-∑' n, priorityWeight (fun j => χ j p) n =
      priorityResidual (priorityList χ c N) p := by
    have hw : (∑' n, priorityWeight (fun j => χ j p) n) =
        ∑ n ∈ Finset.range N, priorityWeight (fun j => χ j p) n := by
      apply tsum_eq_sum
      intro n hn
      rw [priorityWeight, hpz n (by simpa only [Finset.mem_range, not_lt] using hn), zero_mul]
    rw [hw, priorityWeight_sum, priorityList_residual]
    ring
  rw [hlocal.fderiv_eq, hcoef]
  have hfinite := priorityBlend_derivative_bound hX hXb hL
  rw [priorityList_derivative_cost] at hfinite
  apply hfinite.trans
  apply mul_le_mul_of_nonneg_left (hs.sum_le_tsum (Finset.range N) (fun n _ => norm_nonneg _))
  linarith [norm_nonneg (X p)]

end CircleDomainRigidity

end

end OAI
