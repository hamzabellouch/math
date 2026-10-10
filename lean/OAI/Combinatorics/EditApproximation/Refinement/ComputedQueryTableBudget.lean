import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryReadBudget
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryWarmupBudget
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryBudgetAlgebra
import OAI.Combinatorics.EditApproximation.Queries.QueryChargedTableCost

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryLocalProgramBitDegree queryCallbackShellDegree queryInitialWarmupDegree

def computedActiveQueryDegree : ℕ := computedQueryProgramDegree (computedQueryReadDegree 1)

def computedActiveQueryBudget (N J t : ℕ) : ℕ :=
  BinaryFraction.queryLocalProgramBitBudget (integerParameters N).M N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N) (heightExponent N / 20) (smallLogExponent N)
    (inputHeight N ^ 8)
    (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
      (coarseExponent (inputSmallLog N) + 1))) t
    (BinaryFraction.queryPhysicalDataBudget (integerParameters N).T J (inputHeight N ^ 8) (inputHeight N ^ 3)
      (50 * inputHeight N ^ 8 + 24)
      (BinaryFraction.queryFamilySourceReadBudget J (inputHeight N ^ 8) (50 * inputHeight N ^ 8 + 25)))

theorem computedActiveQueryBudget_cap :
    ∀ᶠ N : ℕ in atTop, ∀ J t : ℕ, J ≤ inputHeight N → t ≤ inputHeight N ^ 2 →
      computedActiveQueryBudget N J t ≤ computedLocalKernelBudget computedActiveQueryDegree N := by
  filter_upwards [computedQueryReadBudget_cap 1, computedQueryProgramBudget_cap (computedQueryReadDegree 1),
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hread hprogram hell
  intro J t hJ ht
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  have hg := computed_kernel_guard_cost N hH
  have hT : (integerParameters N).T ≤ inputHeight N ^ 2 := by
    have h := computed_history_budget_le_height_sq N (by omega)
    omega
  have hd := hread (integerParameters N).T J (inputHeight N ^ 8) (inputHeight N ^ 3)
    (50 * inputHeight N ^ 8 + 24) (50 * inputHeight N ^ 8 + 25) hT hJ le_rfl le_rfl
    (by omega) (by omega)
  exact hprogram t _ ht hd

def computedTableQueryDegree : ℕ := max 2 (max (computedQueryWarmupDegree 1) computedActiveQueryDegree) + 1

def computedTableQueryBudget (N Amax J symbolBits positionBits t : ℕ) : ℕ :=
  queryChargedTableBitBudget (integerParameters N).M (integerParameters N).P (inputSmallLog N)
    Amax (inputHeight N ^ 2) J symbolBits positionBits (inputHeight N ^ 8) 1
    (computedActiveQueryBudget N J t)

theorem computedTableQueryBudget_cap :
    ∀ᶠ N : ℕ in atTop, ∀ Amax J symbolBits positionBits t : ℕ,
      Amax ≤ computedLocalKernelBudget 1 N → J ≤ inputHeight N →
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 → t ≤ inputHeight N ^ 2 →
      computedTableQueryBudget N Amax J symbolBits positionBits t ≤
        computedLocalKernelBudget computedTableQueryDegree N := by
  filter_upwards [computedActiveQueryBudget_cap, computedQueryWarmupBudget_cap 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hactive hwarm hell
  intro Amax J symbolBits positionBits t hA hJ hs hp ht
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  have hg := computed_kernel_guard_cost N hH
  have hw := hwarm Amax (inputHeight N ^ 2) J symbolBits positionBits 2 hA le_rfl hJ hs hp (by omega)
  have ha := hactive J t hJ ht
  let D := max 2 (max (computedQueryWarmupDegree 1) computedActiveQueryDegree)
  have hover : 80 * (inputHeight N ^ 8 + 1) ≤ computedLocalKernelBudget 2 N := by
    have hS : 2 ≤ computedLocalKernelBudget 1 N := by omega
    have hsq : computedLocalKernelBudget 2 N = (computedLocalKernelBudget 1 N) ^ 2 := by
      unfold computedLocalKernelBudget localKernelPowerExponent
      simp only [Nat.mul_one, pow_mul]
    rw [hsq]
    nlinarith only [hg, hS]
  have hbound := computedLocalKernelBudget_three N D _ _ _ (by omega)
    (hover.trans (computedLocalKernelBudget_mono N 2 D (Nat.le_max_left _ _)))
    (hw.trans (computedLocalKernelBudget_mono N (computedQueryWarmupDegree 1) D
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))))
    (ha.trans (computedLocalKernelBudget_mono N computedActiveQueryDegree D
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
  exact hbound

end EditApproximation

end OAI
