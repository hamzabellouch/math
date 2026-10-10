import OAI.Analysis.CircleDomains.Selection.MarkedFiniteHitSplit
import OAI.Analysis.CircleDomains.Probability.MarkedFusionKernel
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace OAI

/-! The finite fusion split with closed nonsmall children. The weighted estimate
holds for every simultaneous choice from the children; their diameters can be
prescribed arbitrarily small. -/

open Set Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.MarkedHit

theorem exists_closed_nonsmall_hit_split
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
    [MetricSpace Z] [SecondCountableTopology Z]
    (law : Z → ProbabilityMeasure C(PathTime, Y)) (hlaw : Continuous law)
    {A : Set Z} (hAclosed : IsClosed A) {C ε η r : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (hη : 0 < η) (hr : 0 < r)
    (n : ℕ) [Nonempty (HitConfiguration X n r)] (hA : ¬HitTestSmall ι law C A) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (D : Fin k → Set Z),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, IsClosed (D i) ∧ D i ⊆ A ∧ ¬HitTestSmall ι law C (D i) ∧
        ∀ x ∈ D i, ∀ y ∈ D i, dist x y ≤ η) ∧
      ∀ z : Fin k → Z, (∀ i, z i ∈ D i) →
        ∀ p : HitConfiguration X n r,
          ∑ i, w i * weightedConfigurationHits ι law (z i) p < C + ε := by
  obtain ⟨K, hKA, hKclosed, hKn, _, hKlocal⟩ :=
    exists_closed_hit_test_kernel ι law C hAclosed hA
  obtain ⟨k, z, w, hzK, hw, hw1, hbound⟩ :=
    exists_finite_hit_configuration_split ι law hlaw hC (by positivity : 0 < ε / 2) hr n hKn
  let F : (Fin k → Z) × HitConfiguration X n r → ℝ := fun q =>
    ∑ i, w i * weightedConfigurationHits ι law (q.1 i) q.2
  have hF : UpperSemicontinuous F := by
    apply upperSemicontinuous_sum
    intro i _
    have hc : Continuous (fun q : (Fin k → Z) × HitConfiguration X n r =>
        (q.1 i, q.2)) :=
      (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)
    have hi := (weightedConfigurationHits_upperSemicontinuous ι hlaw n r).comp hc
    exact upperSemicontinuous_nonnegative_mul upperSemicontinuous_const hi
      (fun _ => hw i) (fun _ => weightedConfigurationHits_nonneg ι law _ _)
  have hU : IsOpen {y : Fin k → Z | ∀ p, F (y, p) < C + ε} :=
    isOpen_forall_compact_upper_bound hF (C + ε)
  have hzU : z ∈ {y : Fin k → Z | ∀ p, F (y, p) < C + ε} := by
    intro p
    exact lt_of_le_of_lt (hbound p) (by linarith)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU z hzU
  let δ := min (ρ / 2) (η / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  let D : Fin k → Set Z := fun i => K ∩ closedBall (z i) δ
  refine ⟨k, w, D, hw, hw1, ?_, ?_⟩
  · intro i
    refine ⟨hKclosed.inter isClosed_closedBall, inter_subset_left.trans hKA, ?_, ?_⟩
    · intro hs
      apply hKlocal (z i) (hzK i) (ball (z i) δ) isOpen_ball (mem_ball_self hδ)
      exact HitTestSmall.mono ι hs (inter_subset_inter_right K ball_subset_closedBall)
    · intro x hx y hy
      have hxδ := mem_closedBall.mp hx.2
      have hyδ := mem_closedBall.mp hy.2
      have hdη : δ ≤ η / 2 := min_le_right _ _
      have ht := dist_triangle x (z i) y
      rw [dist_comm (z i) y] at ht
      linarith
  · intro y hy p
    have hdist : dist y z ≤ δ := (dist_pi_le_iff hδ.le).mpr fun i => mem_closedBall.mp (hy i).2
    have hδρ : δ < ρ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ)
    exact hρU (mem_ball.mpr (hdist.trans_lt hδρ)) p

/-- Empty configuration spaces impose no test, but still admit a small closed child. -/
theorem exists_closed_nonsmall_hit_split_all
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
    [MetricSpace Z] [SecondCountableTopology Z]
    (law : Z → ProbabilityMeasure C(PathTime, Y)) (hlaw : Continuous law)
    {A : Set Z} (hAclosed : IsClosed A) {C ε η r : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) (hη : 0 < η) (hr : 0 < r)
    (n : ℕ) (hA : ¬HitTestSmall ι law C A) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (D : Fin k → Set Z),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, IsClosed (D i) ∧ D i ⊆ A ∧ ¬HitTestSmall ι law C (D i) ∧
        ∀ x ∈ D i, ∀ y ∈ D i, dist x y ≤ η) ∧
      ∀ z : Fin k → Z, (∀ i, z i ∈ D i) →
        ∀ p : HitConfiguration X n r,
          ∑ i, w i * weightedConfigurationHits ι law (z i) p < C + ε := by
  classical
  cases isEmpty_or_nonempty (HitConfiguration X n r) with
  | inr hn => exact exists_closed_nonsmall_hit_split ι law hlaw hAclosed hC hε hη hr n hA
  | inl hn =>
    obtain ⟨K, hKA, hKclosed, _, ⟨z, hz⟩, hKlocal⟩ :=
      exists_closed_hit_test_kernel ι law C hAclosed hA
    let D := K ∩ closedBall z (η / 2)
    have hD : ¬HitTestSmall ι law C D := by
      intro hs
      apply hKlocal z hz (ball z (η / 2)) isOpen_ball (mem_ball_self (by positivity))
      exact HitTestSmall.mono ι hs (inter_subset_inter_right K ball_subset_closedBall)
    refine ⟨1, fun _ => 1, fun _ => D, by simp, by simp, ?_, ?_⟩
    · intro i
      refine ⟨hKclosed.inter isClosed_closedBall, inter_subset_left.trans hKA, hD, ?_⟩
      intro x hx y hy
      have hx' := mem_closedBall.mp hx.2
      have hy' := mem_closedBall.mp hy.2
      have ht := dist_triangle x z y
      rw [dist_comm z y] at ht
      linarith
    · intro y hy p
      exact isEmptyElim p

end CircleDomainRigidity.MarkedHit

end

end OAI
