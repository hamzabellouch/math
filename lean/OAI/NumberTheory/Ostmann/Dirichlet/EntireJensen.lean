import OAI.NumberTheory.Ostmann.Dirichlet.LocalZeroCount

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open Set MeromorphicOn
namespace Ostmann.Dirichlet

lemma entire_sum_analyticOrder_le_jensen (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
    (S : Finset ℂ) {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : 1 ≤ M) (hcenter : f c ≠ 0)
    (hS : ∀ z ∈ S, z ∈ Metric.closedBall c r)
    (hbound : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) :
    (∑ z ∈ S, ((analyticOrderAt f z).toNat : ℝ)) ≤
      Real.log (M / ‖f c‖) / Real.log (R / r) := by
  classical
  have htop (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
    intro hz
    have he : f = 0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf).mp hz
    exact hcenter (congrFun he c)
  have ha : AnalyticOnNhd ℂ f (Metric.closedBall c |R|) := fun z _ => hf z
  have har : AnalyticOnNhd ℂ f (Metric.closedBall c r) := fun z _ => hf z
  let D := MeromorphicOn.divisor f (Metric.closedBall c r)
  have hfin : Function.HasFiniteSupport D := D.finiteSupport (isCompact_closedBall c r)
  let U : Finset ℂ := S ∪ hfin.toFinset
  have hSU : S ⊆ U := Finset.subset_union_left
  have hDU : Function.support D ⊆ (U : Set ℂ) := by
    intro z hz
    exact Finset.mem_union_right S (hfin.mem_toFinset.mpr hz)
  have hdeq : ∀ z ∈ S, ((analyticOrderAt f z).toNat : ℤ) = D z := by
    intro z hz
    dsimp only [D]
    rw [har.divisor_apply (hS z hz), ← ENat.natCast_toNat (htop z)]
    simp
  have hsum : (∑ z ∈ S, ((analyticOrderAt f z).toNat : ℤ)) ≤ ∑ᶠ z, D z := by
    rw [finsum_eq_finsetSum_of_support_subset D hDU]
    calc
      _ = ∑ z ∈ S, D z := Finset.sum_congr rfl hdeq
      _ ≤ ∑ z ∈ U, D z := Finset.sum_le_sum_of_subset_of_nonneg hSU
        (fun z _ _ => har.divisor_nonneg z)
  have hj := AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M)
    (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos (hr.trans hrR)] using hrR) hM ha hcenter
    (by simpa [abs_of_pos (hr.trans hrR)] using hbound)
  rw [abs_of_pos hr] at hj
  have hsumR : (∑ z ∈ S, ((analyticOrderAt f z).toNat : ℝ)) ≤
      ((∑ᶠ z, D z : ℤ) : ℝ) := by exact_mod_cast hsum
  exact hsumR.trans hj

end Ostmann.Dirichlet

end OAI
