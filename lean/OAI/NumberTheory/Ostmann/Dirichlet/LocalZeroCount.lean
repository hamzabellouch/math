import Mathlib.Analysis.Complex.JensenFormula
import OAI.NumberTheory.Jacobsthal.Primes.UniformDirichletBasepoint
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral
import OAI.NumberTheory.Ostmann.Dirichlet.Tail
import OAI.NumberTheory.Ostmann.Dirichlet.Zeros

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open Set MeasureTheory MeromorphicOn
open scoped Topology

namespace Ostmann.Dirichlet

lemma sum_zeroMultiplicity_le_jensen {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (S : Finset ℂ)
    {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hcenter : χ.LFunction c ≠ 0)
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.closedBall c r)
    (hbound : ∀ z ∈ Metric.sphere c R, ‖χ.LFunction z‖ ≤ M) :
    (∑ ρ ∈ S, (zeroMultiplicity χ ρ : ℝ)) ≤
      Real.log (M / ‖χ.LFunction c‖) / Real.log (R / r) := by
  classical
  have ha : AnalyticOnNhd ℂ χ.LFunction (Metric.closedBall c |R|) :=
    fun z _ => analyticAt_LFunction χ hχ z
  have har : AnalyticOnNhd ℂ χ.LFunction (Metric.closedBall c r) :=
    fun z _ => analyticAt_LFunction χ hχ z
  let D := MeromorphicOn.divisor χ.LFunction (Metric.closedBall c r)
  have hfin : Function.HasFiniteSupport D := D.finiteSupport (isCompact_closedBall c r)
  let U : Finset ℂ := S ∪ hfin.toFinset
  have hSU : S ⊆ U := Finset.subset_union_left
  have hDU : Function.support D ⊆ (U : Set ℂ) := by
    intro z hz
    exact Finset.mem_union_right S (hfin.mem_toFinset.mpr hz)
  have hdeq : ∀ ρ ∈ S, (zeroMultiplicity χ ρ : ℤ) = D ρ := by
    intro ρ hρ
    dsimp only [D, zeroMultiplicity]
    rw [har.divisor_apply (hS ρ hρ),
      ← ENat.natCast_toNat (analyticOrderAt_LFunction_ne_top χ hχ ρ)]
    simp
  have hsum : (∑ ρ ∈ S, (zeroMultiplicity χ ρ : ℤ)) ≤ ∑ᶠ ρ, D ρ := by
    rw [finsum_eq_finsetSum_of_support_subset D hDU]
    calc
      _ = ∑ ρ ∈ S, D ρ := Finset.sum_congr rfl hdeq
      _ ≤ ∑ ρ ∈ U, D ρ := Finset.sum_le_sum_of_subset_of_nonneg hSU
        (fun ρ _ _ => har.divisor_nonneg ρ)
  have hj := AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M)
    (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos (hr.trans hrR)] using hrR) hM ha hcenter
    (by simpa [abs_of_pos (hr.trans hrR)] using hbound)
  rw [abs_of_pos hr] at hj
  have hsumR : (∑ ρ ∈ S, (zeroMultiplicity χ ρ : ℝ)) ≤ ((∑ᶠ ρ, D ρ : ℤ) : ℝ) := by
    exact_mod_cast hsum
  exact hsumR.trans hj

lemma norm_LFunction_le_partial_sum_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ q * ‖s‖ / s.re := by
  have he : χ.LFunction s = s * ∫ t : ℝ in Ioi 1, partialSumKernel χ s t :=
    LFunction_eq_partial_sum_integral_of_re_pos χ hχ hs
  rw [he, norm_mul]
  have hi := norm_tail_integral_le χ hχ hs zero_lt_one
  simp only [Real.one_rpow, mul_one] at hi
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg s)).trans_eq (by ring)

end Ostmann.Dirichlet

end OAI
