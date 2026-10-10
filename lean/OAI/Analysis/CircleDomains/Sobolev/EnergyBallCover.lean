import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

/-! A countable small-cost ball cover obtained from a local energy payment.
Only the plane's sup metric and the usual fourfold Vitali enlargement are used. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma energy_ball_cover {A : Set (ℝ × ℝ)} {r : (ℝ × ℝ) → ℝ}
    (hr : ∀ x ∈ A, 0 < r x) (hsmall : ∀ x ∈ A, r x ≤ 1)
    (μ : Measure (ℝ × ℝ)) (C : ℝ≥0∞)
    (hpay : ∀ x ∈ A, ENNReal.ofReal (r x) ≤ C * μ (closedBall x (r x))) :
    ∃ U : Set (ℝ × ℝ), U ⊆ A ∧ U.Countable ∧
      A ⊆ ⋃ x : U, closedBall (x : ℝ × ℝ) (4*r x) ∧
      (∑' x : U, ENNReal.ofReal (r x)) ≤ C * μ univ := by
  obtain ⟨U,hUA,hdj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    A id r 1 hsmall 4 (by norm_num)
  have hc : U.Countable :=
    (hdj.mono (fun _ => ball_subset_closedBall)).countable_of_isOpen
      (fun _ _ => isOpen_ball) (fun x hx => nonempty_ball.mpr (hr x (hUA hx)))
  have : Countable U := hc.to_subtype
  refine ⟨U,hUA,hc,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨⟨y,hy⟩, hxy (mem_closedBall_self (hr x hx).le)⟩
  · calc
      _ ≤ ∑' x : U, C * μ (closedBall (x : ℝ × ℝ) (r x)) :=
        ENNReal.tsum_le_tsum (fun x => hpay x (hUA x.property))
      _ = C * μ (⋃ x : U, closedBall (x : ℝ × ℝ) (r x)) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion]
        · exact hdj.subtype _ _
        · exact fun _ => isClosed_closedBall.measurableSet
      _ ≤ C * μ univ := mul_le_mul' le_rfl (measure_mono (subset_univ _))

end CircleDomainRigidity

end

end OAI
