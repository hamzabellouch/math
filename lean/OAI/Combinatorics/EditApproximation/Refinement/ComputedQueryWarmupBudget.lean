import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupUniformCost
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryProgramWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryNumericZero

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryInitialWarmupDegree queryInitialWarmupPrimitiveDegree queryInitialWarmupBitDegree queryChargedWarmupBitBudget

def computedQueryWarmupDegree (K : ℕ) : ℕ := (K + 1) * queryInitialWarmupDegree

theorem computedQueryWarmupBudget_cap (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ Amax copies J symbolBits positionBits C : ℕ,
      Amax ≤ computedLocalKernelBudget 1 N → copies ≤ inputHeight N ^ 2 →
      J ≤ inputHeight N → symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      C ≤ computedLocalKernelBudget K N →
      queryChargedWarmupBitBudget (integerParameters N).M (integerParameters N).P (inputSmallLog N)
        Amax copies J symbolBits positionBits (inputHeight N ^ 8) C ≤
        computedLocalKernelBudget (computedQueryWarmupDegree K) N := by
  filter_upwards [computedQueryNumeric_zero,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hnum hell
  intro Amax copies J symbolBits positionBits C hA hc hJ hs hp hC
  let H := inputHeight N
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let L := (100 * M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := H ^ L
  let X := S ^ (K + 1)
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hpos : 0 < H := lt_of_lt_of_le (by decide : 0 < 64) hH
  have hL : 8 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hHS : H ≤ S := Nat.le_pow ((by decide : 1 ≤ 8).trans hL)
  have hSX : S ≤ X := Nat.le_pow (Nat.succ_le_succ (Nat.zero_le K))
  have h8S : H ^ 8 ≤ S := Nat.pow_le_pow_right hpos hL
  have h2S : H ^ 2 ≤ S := Nat.pow_le_pow_right hpos ((by decide : 2 ≤ 8).trans hL)
  have h3S : H ^ 3 ≤ S := Nat.pow_le_pow_right hpos ((by decide : 3 ≤ 8).trans hL)
  have hCX : C ≤ X := by
    apply hC.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hpos (Nat.mul_le_mul_left L (Nat.le_succ K))
  have hAS : Amax ≤ S := by
    simpa only [S, H, L, M, computedLocalKernelBudget, localKernelPowerExponent, Nat.mul_one] using hA
  have hAX : Amax ≤ X := hAS.trans hSX
  have h := queryChargedWarmupBitBudget_uniform_cap M P (inputSmallLog N) Amax copies J
    symbolBits positionBits (H ^ 8) C X (hH.trans (hHS.trans hSX))
    (hnum.arityCap.trans hSX) (hnum.precisionCap.trans hSX)
    ((computed_smallLog_le_height N).trans (hHS.trans hSX)) hAX
    (hc.trans (h2S.trans hSX)) (hJ.trans (hHS.trans hSX))
    (hs.trans (h3S.trans hSX)) (hp.trans (h3S.trans hSX)) (h8S.trans hSX) hCX
    (hnum.actionCap.trans hSX) (hnum.cartesianCap.trans hSX)
  simpa only [X, S, H, L, computedLocalKernelBudget, localKernelPowerExponent,
    computedQueryWarmupDegree, ← pow_mul, Nat.mul_assoc] using h

end EditApproximation

end OAI
