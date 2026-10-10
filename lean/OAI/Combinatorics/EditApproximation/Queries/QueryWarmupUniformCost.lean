import OAI.Combinatorics.EditApproximation.Queries.QueryInitialWarmupPolynomial

namespace OAI

namespace EditApproximation

attribute [local irreducible] preparedCachedInitialBitDegree preparedMedianBitDegree
  preparedWarmupBitDegree queryInitialWarmupBitDegree

def queryInitialWarmupPrimitiveDegree : ℕ :=
  max 1 (max preparedCachedInitialBitDegree (max preparedMedianBitDegree preparedWarmupBitDegree))

def queryInitialWarmupDegree : ℕ :=
  16 * queryInitialWarmupPrimitiveDegree * queryInitialWarmupBitDegree

theorem queryChargedWarmupBitBudget_uniform_cap (M P F Amax copies J symbolBits positionBits B C X : ℕ)
    (hX : 64 ≤ X) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (hA : Amax ≤ X)
    (hc : copies ≤ X) (hJ : J ≤ X) (hs : symbolBits ≤ X) (hp : positionBits ≤ X)
    (hB : B ≤ X) (hC : C ≤ X)
    (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C ≤
      X ^ queryInitialWarmupDegree := by
  have hpos : 0 < X := by omega
  have hXX : X ≤ X ^ 16 := Nat.le_pow (by decide)
  have hB4 : B + 4 ≤ X ^ 16 := by
    have : B + 4 ≤ X ^ 2 := by nlinarith only [hB, hX]
    exact this.trans (Nat.pow_le_pow_right hpos (by decide))
  have hside : 64 * Amax ^ 2 * P + 2 ≤ X ^ 16 := by
    have hprod := Nat.mul_le_mul (Nat.pow_le_pow_left hA 2) hP
    have hcoef : 66 ≤ X ^ 2 := by nlinarith only [hX]
    calc
      _ ≤ 66 * (X ^ 2 * X) := by nlinarith only [hprod, hX]
      _ ≤ X ^ 2 * (X ^ 2 * X) := Nat.mul_le_mul_right _ hcoef
      _ = X ^ 5 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hpos (by decide)
  have hrepSide : 64 * F * P + 2 ≤ X ^ 4 := by
    have hprod := Nat.mul_le_mul hF hP
    have hcoef : 66 ≤ X ^ 2 := by nlinarith only [hX]
    calc
      _ ≤ 66 * X ^ 2 := by nlinarith only [hprod, hX]
      _ ≤ X ^ 2 * X ^ 2 := Nat.mul_le_mul_right _ hcoef
      _ = _ := by ring
  have hrep : (B + 1) * (64 * F * P + 2) ^ 2 ≤ X ^ 16 := by
    calc
      _ ≤ X ^ 2 * (X ^ 4) ^ 2 := Nat.mul_le_mul (by nlinarith only [hB, hX])
        (Nat.pow_le_pow_left hrepSide 2)
      _ = X ^ 10 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hpos (by decide)
  have h16 : 2 ≤ X ^ 16 := (by omega : 2 ≤ X).trans hXX
  have hi := cachedInitialProgramBitBudget_fixedPower P Amax (B + 2) (X ^ 16) h16 (by omega) hside
  have hm := seedMedianBitBudget_fixedPower copies B (X ^ 16) h16 (hc.trans hXX) (hB.trans hXX)
  have hw := cachedWarmupBitBudget_fixedPower M P F B (X ^ 16) h16 (hM.trans hXX)
    (hP.trans hXX) (hF.trans hXX) hB4 hrep (hV.trans hXX) (hCart.trans hXX)
  have hid : preparedCachedInitialBitDegree ≤ queryInitialWarmupPrimitiveDegree := by
    unfold queryInitialWarmupPrimitiveDegree; omega
  have hmd : preparedMedianBitDegree ≤ queryInitialWarmupPrimitiveDegree := by
    unfold queryInitialWarmupPrimitiveDegree; omega
  have hwd : preparedWarmupBitDegree ≤ queryInitialWarmupPrimitiveDegree := by
    unfold queryInitialWarmupPrimitiveDegree; omega
  have hbase : X ≤ (X ^ 16) ^ queryInitialWarmupPrimitiveDegree :=
    hXX.trans (Nat.le_pow (Nat.le_max_left _ _))
  have hY : 2 ≤ (X ^ 16) ^ queryInitialWarmupPrimitiveDegree := (by omega : 2 ≤ X).trans hbase
  have hw0 : BinaryFraction.localWarmupBitBudget M P F B ≤ (X ^ 16) ^ preparedWarmupBitDegree := by
    omega
  have hwp : BinaryFraction.localWarmupBitBudget M P F B ≤
      (X ^ 16) ^ queryInitialWarmupPrimitiveDegree :=
    hw0.trans (Nat.pow_le_pow_right (pow_pos hpos 16) hwd)
  have h := queryChargedWarmupBitBudget_fixedPower M P F Amax copies J symbolBits positionBits B C
    ((X ^ 16) ^ queryInitialWarmupPrimitiveDegree) hY
    (hM.trans hbase) (hP.trans hbase) (hF.trans hbase) (hA.trans hbase) (hc.trans hbase)
    (hJ.trans hbase) (hs.trans hbase) (hp.trans hbase) (hB.trans hbase) (hC.trans hbase)
    (hi.trans (Nat.pow_le_pow_right (by positivity) hid))
    (hm.trans (Nat.pow_le_pow_right (by positivity) hmd)) hwp
  simpa only [← pow_mul, queryInitialWarmupDegree] using h

end EditApproximation

end OAI
