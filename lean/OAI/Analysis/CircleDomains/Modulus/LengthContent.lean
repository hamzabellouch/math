import OAI.Analysis.CircleDomains.Sobolev.EnergyBallCover
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! One-dimensional Hausdorff content and the energy-cover bound used
for continuous Sobolev scalar functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def lengthContent {X : Type*} [EMetricSpace X] : OuterMeasure X :=
  OuterMeasure.ofFunction ediam ediam_empty

lemma lengthContent_le_ediam {X : Type*} [EMetricSpace X] (S : Set X) :
    lengthContent S ≤ ediam S := OuterMeasure.ofFunction_le S

lemma lengthContent_closedBall_le (x : ℝ × ℝ) (r : ℝ) :
    lengthContent (closedBall x r) ≤ ENNReal.ofReal (2*r) := by
  apply (lengthContent_le_ediam _).trans
  apply ediam_le_of_forall_dist_le
  intro a ha b hb
  have hh := dist_triangle a x b
  rw [dist_comm x b] at hh
  linarith [mem_closedBall.mp ha, mem_closedBall.mp hb]

lemma lengthContent_le_of_energy_payment {A : Set (ℝ × ℝ)} {r : (ℝ × ℝ) → ℝ}
    (hr : ∀ x ∈ A, 0 < r x) (hsmall : ∀ x ∈ A, r x ≤ 1)
    (μ : Measure (ℝ × ℝ)) (C : ℝ≥0∞)
    (hpay : ∀ x ∈ A, ENNReal.ofReal (r x) ≤ C * μ (closedBall x (r x))) :
    lengthContent A ≤ 8*C*μ univ := by
  obtain ⟨U,hUA,hUc,hcover,hcost⟩ := energy_ball_cover hr hsmall μ C hpay
  have : Countable U := hUc.to_subtype
  calc
    lengthContent A ≤ lengthContent (⋃ x : U, closedBall (x : ℝ × ℝ) (4*r x)) :=
      measure_mono hcover
    _ ≤ ∑' x : U, lengthContent (closedBall (x : ℝ × ℝ) (4*r x)) := measure_iUnion_le _
    _ ≤ ∑' x : U, (8 : ℝ≥0∞)*ENNReal.ofReal (r x) := by
      apply ENNReal.tsum_le_tsum
      intro x
      convert lengthContent_closedBall_le (x : ℝ × ℝ) (4*r x) using 1
      rw [show (2:ℝ)*(4*r x) = 8*r x by ring, ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ = 8*∑' x : U, ENNReal.ofReal (r x) := ENNReal.tsum_mul_left
    _ ≤ 8*(C*μ univ) := mul_le_mul' le_rfl hcost
    _ = _ := by rw [mul_assoc]

end CircleDomainRigidity

end

end OAI
