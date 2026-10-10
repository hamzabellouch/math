import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.RealVector

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

noncomputable def Pencil.feasible (B : Pencil n m) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | (B.realEval z).PosSemidef}

lemma Pencil.next_eq_self (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (hy : B.witness y=none) : B.next step mesh y=y := by simp [Pencil.next,hy]

lemma Pencil.next_decrease (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hmesh : 0 < mesh)
    (hstep : (step : ℝ)=r/(n+1))
    (hball : Metric.closedBall c r ⊆ B.feasible)
    (hsmall : 2*(R+step)*((n+1)*mesh)+((n+1)*mesh)^2 ≤ (step : ℝ)^2/2)
    (hy : ‖realVector y-c‖ ≤ R) (hfail : B.witness y ≠ none) :
    ‖realVector (B.next step mesh y)-c‖^2 ≤ ‖realVector y-c‖^2-(step : ℝ)^2/2 := by
  obtain ⟨v,hv⟩ := Option.ne_none_iff_exists'.mp hfail
  have hc : c ∈ B.feasible := hball (Metric.mem_closedBall_self hr.le)
  have ha := B.normal_ne_zero y v hv c hc
  have hm := normalized_margin B.feasible c y (B.normal v) hr.le ha hball
    (fun z hz => by
      have h := B.central_cut y v hv z hz
      change (∑ i : Fin n, (z i-(y i : ℝ))*(B.normal v i : ℝ)) ≤ 0
      simpa only [dotProduct,Pi.sub_apply,mul_comm] using h)
  have hround := realVector_round_error mesh hmesh
    (fun i => y i-step*B.normal v i/l1 (B.normal v))
  rw [realVector_step] at hround
  have hp : 0 ≤ (step : ℝ) := by rw [hstep]; positivity
  have hδ : 0 ≤ (n+1 : ℝ)*(mesh : ℝ) := by positivity
  rw [Pencil.next,hv]
  exact CurrentKS.RationalOptimization.rounded_step_decrease _ c _ _ hp hR hδ hy
    (normalized_norm_le_one _) (hstep ▸ hm) hround hsmall

theorem Pencil.search_feasible (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hmesh : 0 < mesh)
    (hstep : (step : ℝ)=r/(n+1))
    (hball : Metric.closedBall c r ⊆ B.feasible)
    (hsmall : 2*(R+step)*((n+1)*mesh)+((n+1)*mesh)^2 ≤ (step : ℝ)^2/2)
    (hy : ‖realVector y-c‖ ≤ R) (T : ℕ) (hT : R^2 < T*(step : ℝ)^2/2) :
    B.witness ((B.next step mesh)^[T] y)=none := by
  have hp : 0 < (step : ℝ) := by rw [hstep]; positivity
  have hbound : ∀ k : ℕ,
      B.witness ((B.next step mesh)^[k] y)=none ∨
      ‖realVector ((B.next step mesh)^[k] y)-c‖^2 ≤ R^2-k*(step : ℝ)^2/2 := by
    intro k
    induction k with
    | zero =>
      right
      simpa using (sq_le_sq₀ (norm_nonneg _) hR).mpr hy
    | succ k ih =>
      rcases ih with hh|hh
      · left
        rw [Function.iterate_succ_apply',B.next_eq_self _ _ _ hh]
        exact hh
      · by_cases ha : B.witness ((B.next step mesh)^[k] y)=none
        · left
          rw [Function.iterate_succ_apply',B.next_eq_self _ _ _ ha]
          exact ha
        · right
          have hdist : ‖realVector ((B.next step mesh)^[k] y)-c‖ ≤ R := by
            apply (sq_le_sq₀ (norm_nonneg _) hR).mp
            calc
              _ ≤ R^2-k*(step : ℝ)^2/2 := hh
              _ ≤ R^2 := sub_le_self _ (by positivity)
          have hd := B.next_decrease step mesh ((B.next step mesh)^[k] y) c hr hR hmesh
            hstep hball hsmall hdist ha
          rw [Function.iterate_succ_apply']
          push_cast
          linarith
  rcases hbound T with h|h
  · exact h
  · have hn := sq_nonneg ‖realVector ((B.next step mesh)^[T] y)-c‖
    linarith

end CurrentKS.RationalSDP

end OAI
