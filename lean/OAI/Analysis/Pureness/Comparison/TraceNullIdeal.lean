import OAI.Analysis.Pureness.Comparison.UniformTwoNorm
import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.RingTheory.TwoSidedIdeal.Basic

namespace OAI
open Filter Topology
open scoped ENNReal

namespace CuntzComparison

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nonempty (TracialState A)] [Nontrivial A]

abbrev BoundedSequence (A : Type*) [NormedAddCommGroup A] := lp (fun _ : ℕ => A) ∞

def IsTraceNull (ω : Filter ℕ) (x : BoundedSequence A) : Prop :=
  Tendsto (fun l => uniformTwoNorm (x l)) ω (𝓝 0)

omit [Nontrivial A] in
theorem isTraceNull_zero (ω : Filter ℕ) : IsTraceNull ω (0 : BoundedSequence A) := by
  simpa [IsTraceNull] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) ω (𝓝 0))

omit [Nontrivial A] in
theorem IsTraceNull.add {ω : Filter ℕ} {x y : BoundedSequence A}
    (hx : IsTraceNull ω x) (hy : IsTraceNull ω y) : IsTraceNull ω (x + y) := by
  apply squeeze_zero (fun l => uniformTwoNorm_nonneg ((x + y) l))
    (fun l => uniformTwoNorm_add_le (x l) (y l))
  simpa only [add_zero] using Filter.Tendsto.add hx hy

omit [Nonempty (TracialState A)] [Nontrivial A] in
theorem IsTraceNull.neg {ω : Filter ℕ} {x : BoundedSequence A}
    (hx : IsTraceNull ω x) : IsTraceNull ω (-x) := by
  simpa only [IsTraceNull, lp.coeFn_neg, Pi.neg_apply, uniformTwoNorm_neg] using hx

omit [Nontrivial A] in
theorem IsTraceNull.mul_left {ω : Filter ℕ} {x y : BoundedSequence A}
    (hy : IsTraceNull ω y) : IsTraceNull ω (x * y) := by
  apply squeeze_zero (fun l => uniformTwoNorm_nonneg ((x * y) l))
    (fun l => (uniformTwoNorm_mul_left (x l) (y l)).trans
      (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero x l)
        (uniformTwoNorm_nonneg (y l))))
  simpa only [mul_zero] using hy.const_mul ‖x‖

omit [Nontrivial A] in
theorem IsTraceNull.mul_right {ω : Filter ℕ} {x y : BoundedSequence A}
    (hx : IsTraceNull ω x) : IsTraceNull ω (x * y) := by
  apply squeeze_zero (fun l => uniformTwoNorm_nonneg ((x * y) l))
    (fun l => (uniformTwoNorm_mul_right (y l) (x l)).trans
      (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero y l)
        (uniformTwoNorm_nonneg (x l))))
  simpa only [mul_zero] using hx.const_mul ‖y‖

omit [Nonempty (TracialState A)] [Nontrivial A] in
theorem IsTraceNull.star {ω : Filter ℕ} {x : BoundedSequence A}
    (hx : IsTraceNull ω x) : IsTraceNull ω (star x) := by
  simpa only [IsTraceNull, lp.coeFn_star, Pi.star_apply, uniformTwoNorm_star] using hx

theorem IsTraceNull.smul (z : ℂ) {ω : Filter ℕ} {x : BoundedSequence A}
    (hx : IsTraceNull ω x) : IsTraceNull ω (z • x) := by
  apply squeeze_zero (fun l => uniformTwoNorm_nonneg ((z • x) l))
    (fun l => uniformTwoNorm_smul_le z (x l))
  simpa only [mul_zero] using hx.const_mul ‖z‖

noncomputable def traceNullIdeal (ω : Filter ℕ) : TwoSidedIdeal (BoundedSequence A) :=
  .mk' {x | IsTraceNull ω x} (isTraceNull_zero ω)
    (fun hx hy => hx.add hy) (fun hx => hx.neg)
    (fun hy => hy.mul_left) (fun hx => hx.mul_right)

@[simp] theorem mem_traceNullIdeal (ω : Filter ℕ) (x : BoundedSequence A) :
    x ∈ traceNullIdeal ω ↔ IsTraceNull ω x := by
  simp [traceNullIdeal]

theorem isClosed_traceNullIdeal (ω : Filter ℕ) :
    IsClosed (traceNullIdeal (A := A) ω : Set (BoundedSequence A)) := by
  apply isClosed_of_closure_subset
  intro x hx
  apply (mem_traceNullIdeal ω x).mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by linarith)
  have hy0 : IsTraceNull ω y := (mem_traceNullIdeal ω y).mp hy
  have he := Metric.tendsto_nhds.mp hy0 (ε / 2) (by linarith)
  filter_upwards [he] with l hl
  have hcoord : ‖x l - y l‖ ≤ ‖x - y‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) l
  have hdiff := uniformTwoNorm_sub_le (x l) (y l)
  have hupper := (le_abs_self (uniformTwoNorm (x l) - uniformTwoNorm (y l))).trans hdiff
  rw [dist_eq_norm] at hxy
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (uniformTwoNorm_nonneg (x l))] using
    (show uniformTwoNorm (x l) < ε from by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (uniformTwoNorm_nonneg (y l))] at hl
      linarith)

end CuntzComparison

end OAI
