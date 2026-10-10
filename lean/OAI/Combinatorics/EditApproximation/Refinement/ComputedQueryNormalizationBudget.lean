import OAI.Combinatorics.EditApproximation.Queries.QueryRawWidthPolynomial
import OAI.Combinatorics.EditApproximation.Queries.QueryCallbackPolynomial
import OAI.Combinatorics.EditApproximation.Refinement.ComputedLocalKernelWork

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryRawWordDegree queryNormalizationBitDegree

def computedQueryNormalizationDegree (K : ℕ) : ℕ := (K + 1) * queryNormalizationBitDegree

theorem computedQueryNormalizationBudget_cap (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ remaining A B : ℕ, remaining ≤ inputHeight N → B ≤ inputHeight N ^ 3 →
      A ≤ computedLocalKernelBudget K N →
      BinaryFraction.powerDenominatorBitBudget remaining A B ≤
        computedLocalKernelBudget (computedQueryNormalizationDegree K) N := by
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hell
  intro remaining A B hr hB hA
  let H := inputHeight N
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := H ^ L
  let X := S ^ (K + 1)
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hp : 0 < H := by omega
  have hL : 3 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hHS : H ≤ S := Nat.le_pow (by omega)
  have hSX : S ≤ X := Nat.le_pow (by omega)
  have h3S : H ^ 3 ≤ S := Nat.pow_le_pow_right hp hL
  have hAX : A ≤ X := by
    apply hA.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (Nat.mul_le_mul_left L (Nat.le_succ K))
  have h := queryNormalization_fixedPower remaining A B X ((by omega : 2 ≤ H).trans (hHS.trans hSX))
    (hr.trans (hHS.trans hSX)) hAX (hB.trans (h3S.trans hSX))
  apply h.trans_eq
  change ((H ^ L) ^ (K + 1)) ^ queryNormalizationBitDegree = H ^ (L * computedQueryNormalizationDegree K)
  rw [← pow_mul, ← pow_mul]
  congr 1

theorem computedQueryRawWidth_cap :
    ∀ᶠ N : ℕ in atTop,
      BinaryFraction.localWarmupWordBudget (integerParameters N).M (inputHeight N ^ 8) +
        BinaryFraction.preparedKernelWordBudget (integerParameters N).M (inputHeight N ^ 8) ≤
        computedLocalKernelBudget queryRawWordDegree N := by
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hell
  let H := inputHeight N
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := H ^ L
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hL : 8 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hHS : H ≤ S := Nat.le_pow (by omega)
  have hM : (integerParameters N).M ≤ H :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  have h8 : H ^ 8 ≤ S := Nat.pow_le_pow_right (by omega) hL
  have h := queryRawWord_fixedPower (integerParameters N).M (H ^ 8) S
    ((by omega : 2 ≤ H).trans hHS) (hM.trans hHS) h8
  simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using h

end EditApproximation

end OAI
