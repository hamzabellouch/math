import OAI.Combinatorics.EditApproximation.Queries.QueryGatherPolynomial

namespace OAI

namespace EditApproximation

attribute [local irreducible] preparedLocalGroupBitDegree onlineShellDegree physicalShellDegree
  representativeCompleteBitDegree queryGatherBitDegree

def queryPrimitiveBitDegree : ℕ :=
  max 1 (max preparedLocalGroupBitDegree
    (max onlineShellDegree (max physicalShellDegree representativeCompleteBitDegree)))

def queryLocalProgramBitDegree : ℕ := queryPrimitiveBitDegree * queryGatherBitDegree

theorem queryLocalProgramBitBudget_shell_cap (M N P F exponent eM eF B S t W X : ℕ)
    (hX : 2 ≤ X) (hN : Nat.size N ≤ B) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X)
    (he : exponent ≤ X) (hTheta : 2 ^ exponent ≤ X) (hword : 16 * B + 200 ≤ X)
    (hscales : 7 + eM + eF ≤ X) (hS : S ≤ X) (ht : t ≤ X) (hW : W ≤ X)
    (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X)
    (hrep : (B + 1) * (64 * F * P + 2) ^ 2 ≤ X)
    (hgroup : (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ≤ X) :
    BinaryFraction.queryLocalProgramBitBudget M N P F exponent eM eF B S t W ≤
      X ^ queryLocalProgramBitDegree := by
  have hp : 0 < X := by omega
  have hD : 1 ≤ queryPrimitiveBitDegree := Nat.le_max_left _ _
  have hbase : X ≤ X ^ queryPrimitiveBitDegree := Nat.le_pow hD
  have hY : 2 ≤ X ^ queryPrimitiveBitDegree := hX.trans hbase
  have hB : B ≤ X := by omega
  have hg := preparedLocalGroupsBitBudget_fixedPower N M P F exponent eM eF B X
    hX hN hM hP hF he hTheta hword hscales hV hCart
  have ho := preparedLocalOnlineBitBudget_fixedPower M P B X hX hM hB hV
  have hos : BinaryFraction.preparedLocalOnlineBitBudget M P B S ≤
      BinaryFraction.preparedLocalOnlineBitBudget M P B X := by
    unfold BinaryFraction.preparedLocalOnlineBitBudget BinaryFraction.preparedLocalOnlineScaleBitBudget
      BinaryFraction.preparedOnlineBitBudget
    dsimp only
    gcongr
  have hf := physicalContinuationBitBudget_fixedPower M P _ _ (B + 1) (B + 4) X
    hX hM hP hrep hgroup (by omega) (by omega) hV hCart
  have hr := representativeCompleteBitBudget_fixedPower M ((40 * P + 2) ^ (2 * M))
    (4 * (B + 1) + 20) X hX hM hV (by omega)
  have hgd : preparedLocalGroupBitDegree ≤ queryPrimitiveBitDegree := by
    unfold queryPrimitiveBitDegree; omega
  have hod : onlineShellDegree ≤ queryPrimitiveBitDegree := by
    unfold queryPrimitiveBitDegree; omega
  have hfd : physicalShellDegree ≤ queryPrimitiveBitDegree := by
    unfold queryPrimitiveBitDegree; omega
  have hrd : representativeCompleteBitDegree ≤ queryPrimitiveBitDegree := by
    unfold queryPrimitiveBitDegree; omega
  have h := queryLocalProgramBitBudget_fixedPower M N P F exponent eM eF B S t W
    (X ^ queryPrimitiveBitDegree) hY (hM.trans hbase) (hP.trans hbase) (hF.trans hbase)
    (he.trans hbase) ((by omega : eM ≤ X).trans hbase) ((by omega : eF ≤ X).trans hbase)
    (hB.trans hbase) (ht.trans hbase) (hW.trans hbase) (hTheta.trans hbase)
    (hV.trans hbase) (hCart.trans hbase)
    (hg.trans (Nat.pow_le_pow_right hp hgd))
    (hos.trans (ho.trans (Nat.pow_le_pow_right hp hod)))
    (hf.trans (Nat.pow_le_pow_right hp hfd))
    (hr.trans (Nat.pow_le_pow_right hp hrd))
  simpa only [← pow_mul, queryLocalProgramBitDegree] using h

/-- A uniform cap absorbs the finite counts before applying the cost polynomial. -/
theorem queryLocalProgramBitBudget_uniform_cap (M N P F exponent eM eF B S t W X : ℕ)
    (hX : 64 ≤ X) (hN : Nat.size N ≤ B)
    (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (he : exponent ≤ X)
    (heM : eM ≤ X) (heF : eF ≤ X) (hB : B ≤ X) (hS : S ≤ X) (ht : t ≤ X) (hW : W ≤ X)
    (hTheta : 2 ^ exponent ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.queryLocalProgramBitBudget M N P F exponent eM eF B S t W ≤
      X ^ (16 * queryLocalProgramBitDegree) := by
  have hp : 0 < X := by omega
  have hunit : 1 ≤ X := by omega
  have hXX : X ≤ X ^ 16 := Nat.le_pow (by decide)
  have hx2 : X + 1 ≤ X ^ 2 := by nlinarith only [hX]
  have hword : 16 * B + 200 ≤ X ^ 16 := by
    calc
      _ ≤ 216 * X := by omega
      _ ≤ X ^ 2 * X := Nat.mul_le_mul_right _ (by nlinarith only [hX])
      _ = X ^ 3 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hp (by decide)
  have hscales : 7 + eM + eF ≤ X ^ 16 := by
    calc
      _ ≤ 9 * X := by omega
      _ ≤ X ^ 2 := by nlinarith only [hX]
      _ ≤ _ := Nat.pow_le_pow_right hp (by decide)
  have hrepSide : 64 * F * P + 2 ≤ X ^ 4 := by
    have hfp := Nat.mul_le_mul hF hP
    calc
      _ ≤ 66 * X ^ 2 := by nlinarith only [hfp, hX]
      _ ≤ X ^ 2 * X ^ 2 := Nat.mul_le_mul_right _ (by nlinarith only [hX])
      _ = _ := by ring
  have hgroupSide : (32 * F + 2) * 2 ^ exponent + 2 ≤ X ^ 4 := by
    have hft := Nat.mul_le_mul (show 32 * F + 2 ≤ 34 * X by omega) hTheta
    calc
      _ ≤ 36 * X ^ 2 := by nlinarith only [hft, hX]
      _ ≤ X ^ 2 * X ^ 2 := Nat.mul_le_mul_right _ (by nlinarith only [hX])
      _ = _ := by ring
  have hcounts (side : ℕ) (hs : side ≤ X ^ 4) : (B + 1) * side ^ 2 ≤ X ^ 16 := by
    calc
      _ ≤ X ^ 2 * (X ^ 4) ^ 2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hs 2)
      _ = X ^ 10 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hp (by decide)
  have h := queryLocalProgramBitBudget_shell_cap M N P F exponent eM eF B S t W (X ^ 16)
    ((by omega : 2 ≤ X).trans hXX) hN (hM.trans hXX) (hP.trans hXX) (hF.trans hXX)
    (he.trans hXX) (hTheta.trans hXX) hword hscales (hS.trans hXX) (ht.trans hXX) (hW.trans hXX)
    (hV.trans hXX) (hCart.trans hXX) (hcounts _ hrepSide) (hcounts _ hgroupSide)
  simpa only [← pow_mul] using h

end EditApproximation

end OAI
