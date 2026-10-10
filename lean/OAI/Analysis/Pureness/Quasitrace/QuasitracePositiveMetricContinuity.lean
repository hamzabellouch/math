import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuadraticOrder
import OAI.Analysis.Pureness.Quasitrace.QuasitraceBoundedCompletion

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
include hsqrt

lemma exists_metric_delta_sqrt (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : Positive D, T.distance a.1 b.1 < δ →
      |Real.sqrt (T a)-Real.sqrt (T b)| < ε := by
  let U := T (⟨1,zero_le_one⟩ : Positive D)
  have hU : 0 ≤ U := T.nonneg _
  let r := ε^2/(4*(U+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r*(4*(U+1)) = ε^2 := by dsimp [r]; field_simp
  let δ := (ε^2*r/4)^((3:ℝ)⁻¹)
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  have hδ3 : δ^3 = ε^2*r/4 := Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
  refine ⟨δ,hδ,fun a b hab => ?_⟩
  have hq : T (Positive.starMul (a.1-b.1)) < ε^2*r/4 := by
    rw [← T.metricSize_cube,← hδ3]
    exact pow_lt_pow_left₀ hab (T.distance_nonneg _ _) (by decide : 3 ≠ 0)
  have hi : r⁻¹*T (Positive.starMul (a.1-b.1)) < ε^2/4 := by
    have h := mul_lt_mul_of_pos_left hq (inv_pos.mpr hr)
    have he : r⁻¹*(ε^2*r/4) = ε^2/4 := by field_simp
    rwa [he] at h
  have herror : r*U+r⁻¹*T (Positive.starMul (a.1-b.1)) < ε^2 := by nlinarith
  have hq0 := T.nonneg (Positive.starMul (a.1-b.1))
  have hs := Real.sqrt_lt_sqrt (by positivity : 0 ≤ r*U+r⁻¹*T (Positive.starMul (a.1-b.1))) herror
  rw [Real.sqrt_sq hε.le] at hs
  exact (T.sqrt_sub_abs_le_quadratic hsqrt a b r hr).trans_lt hs
end CuntzPureness.PositiveQuasitrace

namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace UniformSpace Filter
open scoped Topology NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

def PositiveMetricPoint := {x : T.MetricPoint hadd // 0 ≤ x.val}
instance positiveMetricPointPseudoMetric : PseudoMetricSpace (T.PositiveMetricPoint hadd) :=
  inferInstanceAs (PseudoMetricSpace {x : T.MetricPoint hadd // 0 ≤ x.val})
def sqrtOnPositive (x : T.PositiveMetricPoint hadd) : ℝ := Real.sqrt (T ⟨x.1.val,x.2⟩)

variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
include hsqrt
lemma sqrtOnPositive_uniformContinuous : UniformContinuous (T.sqrtOnPositive hadd) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := T.exists_metric_delta_sqrt hsqrt ε hε
  refine ⟨δ,hδ,fun x y hxy => ?_⟩
  exact h ⟨x.1.val,x.2⟩ ⟨y.1.val,y.2⟩ hxy

omit hsqrt in

def positiveCompletionValue (x : Completion (T.PositiveMetricPoint hadd)) : ℝ :=
  (Completion.extension (T.sqrtOnPositive hadd) x)^2

lemma positiveCompletionValue_coe (x : T.PositiveMetricPoint hadd) :
    T.positiveCompletionValue hadd x = T ⟨x.1.val,x.2⟩ := by
  rw [positiveCompletionValue,Completion.extension_coe (T.sqrtOnPositive_uniformContinuous hadd hsqrt)]
  exact Real.sq_sqrt (T.nonneg _)

omit hsqrt in
lemma positiveCompletionValue_nonneg (x : Completion (T.PositiveMetricPoint hadd)) :
    0 ≤ T.positiveCompletionValue hadd x := sq_nonneg _
omit hsqrt in
lemma positiveCompletionValue_continuous : Continuous (T.positiveCompletionValue hadd) :=
  Completion.continuous_extension.pow 2
end CuntzPureness.PositiveQuasitrace

end

end OAI
