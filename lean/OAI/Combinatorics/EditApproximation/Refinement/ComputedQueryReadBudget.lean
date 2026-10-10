import OAI.Combinatorics.EditApproximation.Queries.QueryCallbackPolynomial
import OAI.Combinatorics.EditApproximation.Refinement.ComputedLocalKernelWork

namespace OAI

namespace EditApproximation
open Filter

/-- Degree contributed by guards, physical means, and scalar-source reads. -/
def computedQueryReadDegree (K : ℕ) : ℕ := (K + 1) * queryCallbackShellDegree

theorem computedQueryReadBudget_cap (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ T J B V C W : ℕ,
      T ≤ inputHeight N ^ 2 → J ≤ inputHeight N → B ≤ inputHeight N ^ 8 →
      V ≤ inputHeight N ^ 3 → C ≤ computedLocalKernelBudget K N → W ≤ computedLocalKernelBudget K N →
      BinaryFraction.queryPhysicalDataBudget T J B V C (BinaryFraction.queryFamilySourceReadBudget J B W) ≤
        computedLocalKernelBudget (computedQueryReadDegree K) N := by
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hell
  intro T J B V C W hT hJ hB hV hC hW
  let H := inputHeight N
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := H ^ L
  let X := S ^ (K + 1)
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hp : 0 < H := by omega
  have hL : 8 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hSX : S ≤ X := Nat.le_pow (by omega)
  have hHS : H ≤ S := Nat.le_pow (by omega)
  have h8S : H ^ 8 ≤ S := Nat.pow_le_pow_right hp hL
  have h2S : H ^ 2 ≤ S := Nat.pow_le_pow_right hp (by omega)
  have h3S : H ^ 3 ≤ S := Nat.pow_le_pow_right hp (by omega)
  have hcX : C ≤ X := by
    apply hC.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (Nat.mul_le_mul_left L (Nat.le_succ K))
  have hwX : W ≤ X := by
    apply hW.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (Nat.mul_le_mul_left L (Nat.le_succ K))
  have h := queryCallbackShell_fixedPower T J B V C W X
    ((by omega : 2 ≤ H).trans (hHS.trans hSX))
    (hT.trans (h2S.trans hSX)) (hJ.trans (hHS.trans hSX)) (hB.trans (h8S.trans hSX))
    (hV.trans (h3S.trans hSX)) hcX hwX
  apply h.trans_eq
  change ((H ^ L) ^ (K + 1)) ^ queryCallbackShellDegree = H ^ (L * computedQueryReadDegree K)
  rw [← pow_mul, ← pow_mul]
  congr 1

end EditApproximation

end OAI
