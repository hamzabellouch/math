import OAI.Analysis.CircleDomains.Topology.CompactLoopPathFamily
import OAI.Analysis.CircleDomains.Modulus.PathIntervalOscillation
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Pairing

namespace OAI

/-! Minimizing a uniformly convergent sum of interval oscillations.
Every nonconstant loop can strictly decrease one term without increasing
any other term. -/
open Set Function Filter Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

def pathTestInterval (n : ℕ) : Set unitInterval :=
  Icc (denseSeq unitInterval n.unpair.1) (denseSeq unitInterval n.unpair.2)

def loopOscillationTerm (n : ℕ) (g : C(unitInterval, X)) : ℝ :=
  (1 / 2 : ℝ)^n * min 1 (pathOscillation (pathTestInterval n) g)

def loopOscillationCost (g : C(unitInterval, X)) : ℝ :=
  ∑' n, loopOscillationTerm n g

lemma loopOscillationTerm_nonneg (n : ℕ) (g : C(unitInterval, X)) :
    0 ≤ loopOscillationTerm n g :=
  mul_nonneg (by positivity) (le_min zero_le_one Metric.diam_nonneg)

lemma loopOscillationTerm_le (n : ℕ) (g : C(unitInterval, X)) :
    loopOscillationTerm n g ≤ (1 / 2 : ℝ)^n := by
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (mul_one _)

lemma summable_loopOscillationTerm (g : C(unitInterval, X)) :
    Summable (fun n => loopOscillationTerm n g) :=
  Summable.of_nonneg_of_le (fun n => loopOscillationTerm_nonneg n g)
    (fun n => loopOscillationTerm_le n g) summable_geometric_two

lemma continuous_loopOscillationCost : Continuous (loopOscillationCost (X := X)) := by
  apply continuous_tsum (fun n => continuous_const.mul
    (continuous_const.min (continuous_pathOscillation (pathTestInterval n)))) summable_geometric_two
  intro n g
  change ‖loopOscillationTerm n g‖ ≤ (1 / 2 : ℝ)^n
  rw [Real.norm_eq_abs, abs_of_nonneg (loopOscillationTerm_nonneg n g)]
  exact loopOscillationTerm_le n g

lemma loopOscillationCost_erase_lt (g : C(unitInterval, X))
    {a b : unitInterval} (hab : a ≤ b) (heq : g a = g b)
    (hstrict : ∃ n, pathTestInterval n ⊆ Icc a b ∧
      0 < pathOscillation (pathTestInterval n) g) :
    loopOscillationCost (erasePathLoop g a b hab heq) < loopOscillationCost g := by
  obtain ⟨n, hsub, hn⟩ := hstrict
  have hle : ∀ k, loopOscillationTerm k (erasePathLoop g a b hab heq) ≤
      loopOscillationTerm k g := by
    intro k
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact min_le_min_left 1 (pathOscillation_erase_le g hab heq _ _)
  have hz : pathOscillation (pathTestInterval n) (erasePathLoop g a b hab heq) = 0 := by
    apply le_antisymm _ Metric.diam_nonneg
    apply diam_le_of_forall_dist_le le_rfl
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [erasePathLoop_of_mem g hab heq (hsub hu),
      erasePathLoop_of_mem g hab heq (hsub hv), dist_self]
  have hlt : loopOscillationTerm n (erasePathLoop g a b hab heq) < loopOscillationTerm n g := by
    unfold loopOscillationTerm
    rw [hz, min_eq_right zero_le_one, mul_zero]
    exact mul_pos (by positivity) (lt_min zero_lt_one hn)
  exact Summable.tsum_lt_tsum hle hlt (summable_loopOscillationTerm _) (summable_loopOscillationTerm _)

lemma exists_loopOscillation_minimum [CompleteSpace X] (f : C(unitInterval, X)) :
    ∃ g ∈ loopPathFamily f, ∀ h ∈ loopPathFamily f, loopOscillationCost g ≤ loopOscillationCost h :=
  (isCompact_loopPathFamily f).exists_isMinOn ⟨f, mem_loopPathFamily_self f⟩
    continuous_loopOscillationCost.continuousOn

end CircleDomainRigidity

end

end OAI
