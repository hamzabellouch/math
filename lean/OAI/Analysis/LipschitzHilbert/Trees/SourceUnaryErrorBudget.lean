import OAI.Analysis.LipschitzHilbert.Trees.ResidualBudget
import OAI.Analysis.LipschitzHilbert.Trees.PathDrops

namespace OAI

/-! The mask error stays negligible after the phase-mass factor and the
entire logarithmic path-drop sum. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem eventually_source_unary_error_scale (q C R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ L : ℝ in atTop,
      4*Real.sqrt L*(L^q*Real.exp (-L*Real.log L))*(Real.exp (C*Real.sqrt L)*(R*L)) ≤ 1 := by
  filter_upwards [eventually_discarded_residual_small (q+4) C,
    eventually_ge_atTop (max 4 R),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with L hsmall hlarge hlog
  have hL : 4 ≤ L := (le_max_left _ _).trans hlarge
  have hRL : R ≤ L := (le_max_right _ _).trans hlarge
  have hL0 : 0 < L := by linarith
  have hs : Real.sqrt L ≤ L := by
    have := Real.sq_sqrt hL0.le
    have := Real.sqrt_nonneg L
    nlinarith
  have hc : 4*Real.sqrt L*R*L ≤ L^4 := by
    calc
      _ ≤ L*L*L*L := by gcongr
      _ = _ := by ring
  calc
    _ = (4*Real.sqrt L*R*L)*L^q*Real.exp (-L*Real.log L+C*Real.sqrt L) := by
      rw [Real.exp_add]
      ring
    _ ≤ L^4*L^q*Real.exp (-L+C*Real.sqrt L) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL0.le _)
      · apply Real.exp_le_exp.mpr
        nlinarith
      · exact (Real.exp_pos _).le
      · positivity
    _ = Real.exp (-L)*Real.exp (C*Real.sqrt L)*L^(q+4) := by
      rw [Real.exp_add,← Real.rpow_natCast L 4,← Real.rpow_add hL0]
      norm_num only [Nat.cast_ofNat]
      have heq : (4:ℝ)+q = q+4 := by ring
      rw [heq]
      ring
    _ ≤ 1 := hsmall

/-- Uniformly over a finite active prefix and any subcollection of its
indices, the physical off-child contribution costs at most one. -/
theorem eventually_source_unary_error_budget (q C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ → ℝ) (count : ℕ) (S : Finset ℕ),
      S ⊆ Finset.range count → Antitone n →
    ∀ (M p ε Q : ℝ), 1 ≤ M → 0 ≤ p → p ≤ Real.sqrt L →
      0 ≤ ε → ε ≤ L^q*Real.exp (-L*Real.log L) →
      0 ≤ Q → Q ≤ Real.exp (C*Real.sqrt L) →
      (∀ j < count, M < n j) → 0 ≤ n count → Real.log (n 0) ≤ 3*L →
      4*p*ε*(Q*∑ j ∈ S, pathDrop n j) ≤ 1 := by
  filter_upwards [eventually_source_unary_error_scale q C 4 (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L hscale hL
  intro n count S hS hanti M p ε Q hM hp hpL hε hεL hQ hQL hactive hlast hlog
  have hM0 : 0 < M := by linarith
  have hnonneg (j : ℕ) (hj : j ∈ Finset.range count) : 0 ≤ pathDrop n j :=
    pathDrop_nonnegative n j (hM0.trans (hactive j (Finset.mem_range.mp hj)))
      (hanti (Nat.le_succ j))
  have hsum0 : 0 ≤ ∑ j ∈ S, pathDrop n j := Finset.sum_nonneg fun j hj => hnonneg j (hS hj)
  have hsum : (∑ j ∈ S, pathDrop n j) ≤ 4*L := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hS (fun j hj _ => hnonneg j hj)).trans
    by_cases hc : count = 0
    · simp only [hc,Finset.sum_range_zero]
      linarith
    have hn0 := hM0.trans (hactive 0 (Nat.pos_of_ne_zero hc))
    have hlogM : Real.log (n 0/M) ≤ 3*L :=
      (Real.log_le_log (div_pos hn0 hM0) (div_le_self hn0.le hM)).trans hlog
    have hb := active_path_drop_budget n count hM0 hactive hlast
    have hm : max 0 (Real.log (n 0/M)) ≤ 3*L := max_le (by linarith) hlogM
    linarith
  calc
    _ ≤ 4*Real.sqrt L*(L^q*Real.exp (-L*Real.log L))*
        (Real.exp (C*Real.sqrt L)*(4*L)) := by gcongr
    _ ≤ 1 := hscale

end LipschitzHilbert

end

end OAI
