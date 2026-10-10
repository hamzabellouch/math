import OAI.Analysis.KadisonKastler.TracialSequenceState
import OAI.Analysis.Pureness.Completion.ClosedStarIdealQuotientCStar

namespace OAI

/-! # The closed two-norm null ideal of a tracial bounded product -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

def TraceNullSequence (x : VaryingBoundedSequence B) : Prop :=
  Tendsto (fun j => traceTwoNorm (τ j) (x j)) (ω : Filter ℕ) (𝓝 0)

omit [∀ j, Nontrivial (B j)] in
theorem traceNullSequence_add {x y : VaryingBoundedSequence B}
    (hx : TraceNullSequence τ ω x) (hy : TraceNullSequence τ ω y) :
    TraceNullSequence τ ω (x + y) := by
  apply squeeze_zero (fun j => traceTwoNorm_nonneg (τ j) _)
    (fun j => traceTwoNorm_add_le (τ j) (x j) (y j))
  simpa only [add_zero] using hx.add hy

omit [∀ j, Nontrivial (B j)] in
theorem traceNullSequence_mul_left (x : VaryingBoundedSequence B)
    {y : VaryingBoundedSequence B} (hy : TraceNullSequence τ ω y) :
    TraceNullSequence τ ω (x * y) := by
  apply squeeze_zero (fun j => traceTwoNorm_nonneg (τ j) _)
    (fun j => (traceTwoNorm_mul_le_left (τ j) (x j) (y j)).trans
      (mul_le_mul_of_nonneg_right (varyingSequence_norm_apply_le x j)
        (traceTwoNorm_nonneg (τ j) _)))
  simpa only [mul_zero] using hy.const_mul ‖x‖

omit [∀ j, Nontrivial (B j)] in
theorem traceNullSequence_mul_right {x : VaryingBoundedSequence B}
    (hx : TraceNullSequence τ ω x) (y : VaryingBoundedSequence B) :
    TraceNullSequence τ ω (x * y) := by
  apply squeeze_zero (fun j => traceTwoNorm_nonneg (τ j) _)
    (fun j => (traceTwoNorm_mul_le_right (τ j) (x j) (y j)).trans
      (mul_le_mul_of_nonneg_left (varyingSequence_norm_apply_le y j)
        (traceTwoNorm_nonneg (τ j) _)))
  simpa only [zero_mul] using hx.mul_const ‖y‖

theorem isClosed_traceNullSequence :
    IsClosed {x : VaryingBoundedSequence B | TraceNullSequence τ ω x} := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  have hnorm : ‖x - y‖ < ε / 2 := by simpa only [dist_eq_norm] using hxy
  filter_upwards [(Metric.tendsto_nhds.mp hy) (ε / 2) (half_pos hε)] with j hj
  have hyj : traceTwoNorm (τ j) (y j) < ε / 2 := by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (traceTwoNorm_nonneg _ _)] using hj
  have ht : traceTwoNorm (τ j) (x j) ≤ ‖x - y‖ + traceTwoNorm (τ j) (y j) := by
    calc
      _ = traceTwoNorm (τ j) ((x j - y j) + y j) := by rw [sub_add_cancel]
      _ ≤ traceTwoNorm (τ j) (x j - y j) + traceTwoNorm (τ j) (y j) :=
        traceTwoNorm_add_le _ _ _
      _ ≤ ‖x - y‖ + traceTwoNorm (τ j) (y j) :=
        add_le_add ((traceTwoNorm_le_norm (τ j) (x j - y j)).trans
          (varyingSequence_norm_apply_le (x - y) j)) le_rfl
  simpa only [dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (traceTwoNorm_nonneg _ _)] using ht.trans_lt (by linarith)

def traceNullClosedIdeal : CuntzPureness.ClosedStarIdeal (VaryingBoundedSequence B) where
  ideal := TwoSidedIdeal.mk' {x | TraceNullSequence τ ω x}
    (by
      change Tendsto (fun j => traceTwoNorm (τ j) 0) (ω : Filter ℕ) (𝓝 0)
      simpa only [traceTwoNorm, star_zero, zero_mul, map_zero, Complex.zero_re, Real.sqrt_zero]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0)))
    (traceNullSequence_add τ ω)
    (by
      intro x hx
      change TraceNullSequence τ ω (-x)
      change TraceNullSequence τ ω x at hx
      simpa only [TraceNullSequence, lp.coeFn_neg, Pi.neg_apply, traceTwoNorm,
        star_neg, neg_mul_neg] using hx)
    (by intro x y hy; exact traceNullSequence_mul_left τ ω x hy)
    (by intro x y hx; exact traceNullSequence_mul_right τ ω hx y)
  star_mem := by
    intro x hx
    change TraceNullSequence τ ω (star x - 0)
    change TraceNullSequence τ ω (x - 0) at hx
    simpa only [sub_zero, TraceNullSequence, lp.coeFn_star, Pi.star_apply, traceTwoNorm_star] using hx
  isClosed := by
    simpa only [TwoSidedIdeal.coe_mk'] using isClosed_traceNullSequence τ ω

omit [∀ j, Nontrivial (B j)] in
/-- The canonical trace vanishes on the two-norm null ideal. -/
theorem tracialSequenceValue_eq_zero_of_null {x : VaryingBoundedSequence B}
    (hx : TraceNullSequence τ ω x) : tracialSequenceValue τ ω x = 0 := by
  have hlim : Tendsto (fun j => (τ j).toLinearMap (x j)) (ω : Filter ℕ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun j => norm_nonneg _)
      (fun j => (τ j).norm_apply_le_traceTwoNorm (x j)) hx
  exact tendsto_nhds_unique (tendsto_tracialSequenceValue τ ω x) hlim

omit [∀ j, Nontrivial (B j)] in
/-- A square has zero limit trace precisely when its sequence is two-null. -/
theorem tracialSequenceValue_square_eq_zero_iff (x : VaryingBoundedSequence B) :
    tracialSequenceValue τ ω (star x * x) = 0 ↔ TraceNullSequence τ ω x := by
  constructor
  · intro hx
    have hlim := tendsto_tracialSequenceValue τ ω (star x * x)
    rw [hx] at hlim
    have ht := (Real.continuous_sqrt.tendsto 0).comp
      ((Complex.continuous_re.tendsto 0).comp hlim)
    simpa only [TraceNullSequence, Function.comp_def, lp.infty_coeFn_mul, lp.coeFn_star,
      Pi.mul_apply, Pi.star_apply, Complex.zero_re, Real.sqrt_zero, traceTwoNorm] using ht
  · intro hx
    exact tracialSequenceValue_eq_zero_of_null τ ω
      (traceNullSequence_mul_left τ ω (star x) hx)

end

end KadisonKastler

end OAI
