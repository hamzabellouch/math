import OAI.Analysis.Pureness.Quasitrace.QuasitraceValueLimits

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace UniformSpace Filter
open scoped Topology NNReal ComplexStarModule
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)

lemma selfAdjoint_add_bound_nonneg (a : selfAdjoint D) (C : ℝ) (hC : ‖a.1‖ ≤ C) :
    0 ≤ a.1+C • (1 : D) := by
  have ha := a.2.neg_algebraMap_norm_le_self
  rw [Algebra.algebraMap_eq_smul_one] at ha
  have hc : ‖a.1‖ • (1 : D) ≤ C • 1 := smul_le_smul_of_nonneg_right hC zero_le_one
  have h := add_le_add_right ((neg_le_neg hc).trans ha) (C • (1:D))
  simpa [add_comm] using h

lemma selfAdjointValue_shift (a : selfAdjoint D) (C : ℝ) (hC : 0 ≤ C) (ha : ‖a.1‖ ≤ C) :
    T.selfAdjointValue a = T ⟨a.1+C • 1,selfAdjoint_add_bound_nonneg a C ha⟩-
      C*T ⟨1,zero_le_one⟩ := by
  let p : Positive D := ⟨a.1+C • 1,selfAdjoint_add_bound_nonneg a C ha⟩
  let q := Positive.smul (⟨C,hC⟩ : ℝ≥0) (⟨1,zero_le_one⟩ : Positive D)
  have he : a.1 = p.1-q.1 := by change a.1 = a.1+C • 1-C • 1; abel
  have hcomm : Commute p.1 q.1 :=
    ((Commute.one_right a.1).smul_right C).add_left (Commute.refl _)
  rw [T.selfAdjointValue_sub a p q he hcomm]
  exact congrArg (fun x : ℝ => T p - x)
    (T.map_smul (⟨C, hC⟩ : ℝ≥0) (⟨1, zero_le_one⟩ : Positive D))

variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
include hadd hsqrt
lemma selfAdjoint_values_converge (u : ℕ → selfAdjoint D)
    (hu : T.IsMetricCauchy (fun k => (u k).1)) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ k, ‖(u k).1‖ ≤ C) :
    ∃ v : ℝ, Tendsto (fun k => T.selfAdjointValue (u k)) atTop (nhds v) := by
  let p (k : ℕ) : Positive D := ⟨(u k).1+C • 1,selfAdjoint_add_bound_nonneg (u k) C (hb k)⟩
  have hp : T.IsMetricCauchy (fun k => (p k).1) :=
    T.isMetricCauchy_add hadd hu (T.isMetricCauchy_const (C • 1))
  obtain ⟨v,hv0,hv⟩ := T.positive_values_converge hadd hsqrt p hp
  refine ⟨v-C*T ⟨1,zero_le_one⟩,?_⟩
  have he (k : ℕ) : T.selfAdjointValue (u k) = T (p k)-C*T ⟨1,zero_le_one⟩ :=
    T.selfAdjointValue_shift (u k) C hC (hb k)
  simp only [he]
  exact hv.sub_const _
end CuntzPureness.PositiveQuasitrace

end

end OAI
