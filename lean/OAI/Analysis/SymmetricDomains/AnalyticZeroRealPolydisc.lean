import Mathlib
import OAI.Analysis.SymmetricDomains.ProperEventuallyFiberSubset

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem analytic_zero_of_real_interval {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hz : ∀ t : ℝ, |t| < r → f t = 0) : EqOn f 0 (ball 0 r) := by
  apply hf.eqOn_zero_of_preconnected_of_mem_closure (convex_ball (0 : ℂ) r).isPreconnected
    (mem_ball_self hr)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let t := min ε r / 2
  have ht : 0 < t := half_pos (lt_min hε hr)
  have htε : t < ε := lt_of_lt_of_le (half_lt_self (lt_min hε hr)) (min_le_left _ _)
  have htr : t < r := lt_of_lt_of_le (half_lt_self (lt_min hε hr)) (min_le_right _ _)
  refine ⟨(t : ℂ),⟨hz t (by simpa [abs_of_pos ht] using htr),?_⟩,?_⟩
  · simpa using ht.ne'
  · simpa [dist_eq_norm,Complex.norm_real,abs_of_pos ht] using htε

theorem analytic_zero_of_real_polydisc {n : ℕ} {f : (Fin n → ℂ) → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (ball 0 r))
    (hz : ∀ x : Fin n → ℝ, ‖x‖ < r → f (fun i => (x i : ℂ)) = 0) :
    EqOn f 0 (ball 0 r) := by
  classical
  have hgen : ∀ S : Finset (Fin n), ∀ z : Fin n → ℂ, ‖z‖ < r →
      (∀ i ∉ S, (z i).im = 0) → f z = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro z hzr hreal
      have heq : z = fun i => ((z i).re : ℂ) := by
        funext i
        exact Complex.ext rfl (by simpa using hreal i (by simp))
      rw [heq]
      apply hz
      apply (pi_norm_lt_iff hr).mpr
      intro i
      exact (Complex.abs_re_le_norm _).trans_lt ((pi_norm_lt_iff hr).mp hzr i)
    | @insert a S ha ih =>
      intro z hzr hreal
      let g : ℂ → ℂ := fun t => f (Function.update z a t)
      have hupdate : ∀ t : ℂ, ‖t‖ < r → ‖Function.update z a t‖ < r := by
        intro t ht
        apply (pi_norm_lt_iff hr).mpr
        intro i
        by_cases hi : i = a
        · subst i; simpa using ht
        · simpa [Function.update_of_ne hi] using (pi_norm_lt_iff hr).mp hzr i
      have hg : AnalyticOnNhd ℂ g (ball 0 r) := by
        intro t ht
        have haffin : AnalyticAt ℂ (fun t : ℂ => Function.update z a t) t := by
          apply analyticAt_pi_iff.mpr
          intro i
          by_cases hi : i = a
          · subst i
            simp only [Function.update_self]
            exact analyticAt_id
          · simpa only [Function.update_of_ne hi] using (analyticAt_const (𝕜 := ℂ) (v := z i) (x := t))
        have htu : Function.update z a t ∈ ball 0 r := by
          simpa only [mem_ball,dist_zero_right] using
            (hupdate t (by simpa only [mem_ball,dist_zero_right] using ht))
        exact (hf _ htu).comp haffin
      have hgr : ∀ t : ℝ, |t| < r → g t = 0 := by
        intro t ht
        apply ih _ (hupdate t (by simpa using ht))
        intro i hi
        by_cases hia : i = a
        · subst i; simp
        · simpa only [Function.update_of_ne hia] using hreal i (by simp [hia,hi])
      have hzero := analytic_zero_of_real_interval hr hg hgr (by
        simpa only [mem_ball,dist_zero_right] using (pi_norm_lt_iff hr).mp hzr a)
      simpa only [g, Function.update_eq_self, Pi.zero_apply] using hzero
  intro z hzball
  exact hgen Finset.univ z (by simpa only [mem_ball,dist_zero_right] using hzball)
    (by intro i hi; exact (hi (Finset.mem_univ i)).elim)

end Release061

end

end OAI
