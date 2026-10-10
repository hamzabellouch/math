import OAI.Analysis.Pureness.Comparison.TraceNullIdeal

namespace OAI
open Filter Topology
open scoped ENNReal

namespace CuntzComparison

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace TracialState

theorem norm_apply_le_twoNorm (τ : TracialState A) (a : A) :
    ‖τ.toPositiveLinearMap a‖ ≤ τ.twoNorm a := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (τ.toPositiveLinearMap.toPreGNS 1)
    (τ.toPositiveLinearMap.toPreGNS a)
  have hone : ‖τ.toPositiveLinearMap.toPreGNS 1‖ = 1 := τ.twoNorm_one
  simpa only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, hone, twoNorm] using h

theorem norm_apply_le_norm (τ : TracialState A) (a : A) :
    ‖τ.toPositiveLinearMap a‖ ≤ ‖a‖ :=
  (τ.norm_apply_le_twoNorm a).trans (τ.twoNorm_le_norm a)

theorem norm_apply_mul_le (τ : TracialState A) (a b : A) :
    ‖τ.toPositiveLinearMap (a * b)‖ ≤ τ.twoNorm a * τ.twoNorm b := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (τ.toPositiveLinearMap.toPreGNS (star a))
    (τ.toPositiveLinearMap.toPreGNS b)
  have h' : ‖τ.toPositiveLinearMap (a * b)‖ ≤ τ.twoNorm (star a) * τ.twoNorm b := by
    simpa only [PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_star, twoNorm] using h
  simpa only [twoNorm_star] using h'

end TracialState

theorem bounded_trace_evaluations (τ : ℕ → TracialState A) (x : BoundedSequence A)
    (l : ℕ) : ‖(τ l).toPositiveLinearMap (x l)‖ ≤ ‖x‖ :=
  ((τ l).norm_apply_le_norm (x l)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero x l)

theorem IsTraceNull.trace_tendsto_zero {ω : Filter ℕ} {x : BoundedSequence A}
    (hx : IsTraceNull ω x) (τ : ℕ → TracialState A) :
    Tendsto (fun l => (τ l).toPositiveLinearMap (x l)) ω (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun l => norm_nonneg _)
    (fun l => ((τ l).norm_apply_le_twoNorm (x l)).trans (twoNorm_le_uniform (τ l) (x l))) hx

theorem trace_difference_tendsto_zero {ω : Filter ℕ} {x y : BoundedSequence A}
    (hxy : IsTraceNull ω (x - y)) (τ : ℕ → TracialState A) :
    Tendsto (fun l => (τ l).toPositiveLinearMap (x l) - (τ l).toPositiveLinearMap (y l))
      ω (𝓝 0) := by
  simpa only [lp.coeFn_sub, Pi.sub_apply, map_sub] using hxy.trace_tendsto_zero τ

end CuntzComparison

end OAI
