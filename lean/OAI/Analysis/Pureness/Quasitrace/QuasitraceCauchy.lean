import OAI.Analysis.Pureness.Quasitrace.QuasitraceMetricContinuity
import Mathlib.Topology.MetricSpace.Cauchy

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)

def IsMetricCauchy (u : ℕ → D) : Prop :=
  Tendsto (fun p : ℕ × ℕ => T.distance (u p.1) (u p.2)) atTop (nhds 0)
def IsMetricNull (u : ℕ → D) : Prop := Tendsto (fun k => T.metricSize (u k)) atTop (nhds 0)

lemma isMetricCauchy_const (x : D) : T.IsMetricCauchy (fun _ => x) := by
  simp only [IsMetricCauchy,T.distance_self]; exact tendsto_const_nhds
lemma isMetricCauchy_star {u : ℕ → D} (hu : T.IsMetricCauchy u) :
    T.IsMetricCauchy (fun k => star (u k)) := by
  simpa only [IsMetricCauchy,T.distance_star] using hu
lemma isMetricCauchy_neg {u : ℕ → D} (hu : T.IsMetricCauchy u) :
    T.IsMetricCauchy (fun k => -u k) := by
  have he (x y : D) : T.distance (-x) (-y) = T.distance x y := by
    change T.metricSize (-x - -y) = T.metricSize (x-y)
    rw [show -x - -y = -(x-y) from by abel,T.metricSize_neg]
  simpa only [IsMetricCauchy,he] using hu
lemma isMetricCauchy_smul {u : ℕ → D} (hu : T.IsMetricCauchy u) (c : ℂ) :
    T.IsMetricCauchy (fun k => c • u k) := by
  exact squeeze_zero (fun p => T.distance_nonneg _ _) (fun p => T.distance_smul_le c _ _)
    (by simpa using hu.const_mul (‖c‖^(2/3:ℝ)))
lemma isMetricNull_zero : T.IsMetricNull (fun _ => 0) := by
  simp only [IsMetricNull,T.metricSize_zero]; exact tendsto_const_nhds
lemma isMetricNull_star {u : ℕ → D} (hu : T.IsMetricNull u) :
    T.IsMetricNull (fun k => star (u k)) := by simpa only [IsMetricNull,T.metricSize_star] using hu
lemma isMetricNull_neg {u : ℕ → D} (hu : T.IsMetricNull u) :
    T.IsMetricNull (fun k => -u k) := by simpa only [IsMetricNull,T.metricSize_neg] using hu
lemma isMetricNull_smul {u : ℕ → D} (hu : T.IsMetricNull u) (c : ℂ) :
    T.IsMetricNull (fun k => c • u k) := by
  exact squeeze_zero (fun k => T.metricSize_nonneg _) (fun k => T.metricSize_smul_le c _)
    (by simpa using hu.const_mul (‖c‖^(2/3:ℝ)))
lemma isMetricNull_mul_left {u v : ℕ → D} (hv : T.IsMetricNull v)
    (C : ℝ) (hC : 0 ≤ C) (hu : ∀ k, ‖u k‖ ≤ C) :
    T.IsMetricNull (fun k => u k*v k) := by
  refine squeeze_zero (fun k => T.metricSize_nonneg _) (fun k => ?_)
    (show Tendsto (fun k => C^(2/3:ℝ)*T.metricSize (v k)) atTop (nhds 0) by
      simpa using hv.const_mul (C^(2/3:ℝ)))
  exact (T.metricSize_mul_le_left _ _).trans (mul_le_mul
    (Real.rpow_le_rpow (norm_nonneg _) (hu k) (by norm_num)) le_rfl
    (T.metricSize_nonneg _) (Real.rpow_nonneg hC _))
lemma isMetricNull_mul_right {u v : ℕ → D} (hu : T.IsMetricNull u)
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ k, ‖v k‖ ≤ C) :
    T.IsMetricNull (fun k => u k*v k) := by
  have h := T.isMetricNull_mul_left (T.isMetricNull_star hu) C hC
    (show ∀ k, ‖star (v k)‖ ≤ C by simpa using hv)
  simpa only [← star_mul,IsMetricNull,T.metricSize_star] using h

variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
include hadd
lemma isMetricCauchy_add {u v : ℕ → D} (hu : T.IsMetricCauchy u) (hv : T.IsMetricCauchy v) :
    T.IsMetricCauchy (fun k => u k+v k) := by
  exact squeeze_zero (fun p => T.distance_nonneg _ _) (fun p => T.distance_add hadd _ _ _ _)
    (by simpa using hu.add hv)
lemma isMetricNull_add {u v : ℕ → D} (hu : T.IsMetricNull u) (hv : T.IsMetricNull v) :
    T.IsMetricNull (fun k => u k+v k) := by
  exact squeeze_zero (fun k => T.metricSize_nonneg _) (fun k => hadd _ _)
    (by simpa using hu.add hv)
lemma isMetricCauchy_mul {u v : ℕ → D} (hu : T.IsMetricCauchy u) (hv : T.IsMetricCauchy v)
    (C E : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hbu : ∀ k, ‖u k‖ ≤ C) (hbv : ∀ k, ‖v k‖ ≤ E) :
    T.IsMetricCauchy (fun k => u k*v k) := by
  refine squeeze_zero (fun p => T.distance_nonneg _ _) (fun p => ?_)
    (show Tendsto (fun p : ℕ × ℕ => C^(2/3:ℝ)*T.distance (v p.1) (v p.2)+
      E^(2/3:ℝ)*T.distance (u p.1) (u p.2)) atTop (nhds 0) by
      simpa using (hv.const_mul (C^(2/3:ℝ))).add (hu.const_mul (E^(2/3:ℝ))))
  exact (T.distance_mul hadd _ _ _ _).trans (add_le_add
    (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) (hbu p.1) (by norm_num)) le_rfl
      (T.distance_nonneg _ _) (Real.rpow_nonneg hC _))
    (mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) (hbv p.2) (by norm_num)) le_rfl
      (T.distance_nonneg _ _) (Real.rpow_nonneg hE _)))
end CuntzPureness.PositiveQuasitrace

end

end OAI
