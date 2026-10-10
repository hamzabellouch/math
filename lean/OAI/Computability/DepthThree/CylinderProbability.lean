import OAI.Computability.DepthThree.FiniteProbability
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum

namespace OAI

universe uDepth1

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

theorem finiteAvg_eq_pattern (U : Finset V) (σ : Cube V) :
    finiteAvg (fun x : Cube V =>
      if ∀ v ∈ U, x v = σ v then (1 : ℝ) else 0) =
      ((2 : ℝ) ^ U.card)⁻¹ := by
  classical
  let q : V → Bool → ℝ := fun v b => if v ∈ U → b = σ v then 1 else 0
  have hpoint (x : Cube V) :
      (if ∀ v ∈ U, x v = σ v then (1 : ℝ) else 0) = ∏ v, q v (x v) := by
    dsimp [q]
    rw [Fintype.prod_boole]
  have hcoordinate (v : V) :
      finiteAvg (q v) = if v ∈ U then (2 : ℝ)⁻¹ else 1 := by
    by_cases hv : v ∈ U
    · cases hσ : σ v <;>
        norm_num [q, hv, hσ, finiteAvg, Fintype.sum_bool]
    · simp [q, hv]
  calc
    _ = finiteAvg (fun x : Cube V => ∏ v, q v (x v)) := finiteAvg_congr hpoint
    _ = ∏ v, finiteAvg (q v) := finiteAvg_pi_prod q
    _ = ∏ v, if v ∈ U then (2 : ℝ)⁻¹ else 1 := by
      exact Finset.prod_congr rfl (fun v _ => hcoordinate v)
    _ = ((2 : ℝ) ^ U.card)⁻¹ := by
      rw [← Finset.prod_filter]
      have hfilter : Finset.univ.filter (fun v => v ∈ U) = U := by
        ext v
        simp
      rw [hfilter, Finset.prod_const, inv_pow]

theorem finiteAvg_indicator_eq_pattern (U : Finset V) (σ : Cube V) :
    finiteAvg (fun x : Cube V => indicator (decide (∀ v ∈ U, x v = σ v))) =
      ((2 : ℝ) ^ U.card)⁻¹ := by
  refine (finiteAvg_congr fun x => ?_).trans (finiteAvg_eq_pattern U σ)
  by_cases hx : ∀ v ∈ U, x v = σ v <;> simp [indicator, hx]

end DepthThreeLowerBound

end

end OAI
