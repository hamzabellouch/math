import OAI.Combinatorics.EditApproximation.Geometry.PreparedKernelPolynomial

namespace OAI

/-! The complete refinement return includes literal power-denominator
construction, multiplication, division and trimming before cache insertion. -/

namespace EditApproximation

private abbrev CachePoly := FiniteBitPolynomial (Fin 4)
private def cacheSum (M B : CachePoly) : CachePoly :=
  .bitLength M + B + 2 * (1 + M * (B + 1)) + 2
private def cacheConnection (M B : CachePoly) : CachePoly := cacheSum (M + 1) (8 * B + 6)
private def cacheAction (M B : CachePoly) : CachePoly := 8 * (40 * B + 22 + cacheSum M B) + 6
private def cacheRawWidth (M B : CachePoly) : CachePoly :=
  let W := B + 4 + cacheConnection M (B + 4) + (64 * (B + 4) + 54) + 4 * (B + 4) + 2
  32 * (W + 2 * cacheAction M W + 1) + 28
private def cacheReturnPolynomial : CachePoly :=
  let M := .input 0
  let B := .input 1
  let n := .input 2
  let D := .input 3
  (1 + n * (200 * ((n + 1) * (D + 1) + 1) ^ 2)) +
    5000 * (cacheRawWidth M B + (n * D + 1) + 2) ^ 2 + 1

private def cacheEnvironment (M B n D : ℕ) : Fin 4 → ℕ
  | 0 => M
  | 1 => B
  | 2 => n
  | _ => D

def preparedCacheReturnBitDegree : ℕ := cacheReturnPolynomial.degree

def preparedCachedKernelBitDegree : ℕ := max preparedKernelBitDegree preparedCacheReturnBitDegree + 2

attribute [local irreducible] preparedKernelBitDegree preparedCacheReturnBitDegree

theorem preparedCacheReturnBitBudget_fixedPower (M B n D X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hB : B ≤ X) (hn : n ≤ X) (hD : D ≤ X) :
    BinaryFraction.powerDenominatorBitBudget n (BinaryFraction.preparedKernelWordBudget M B) D ≤
      X ^ preparedCacheReturnBitDegree := by
  have heval : cacheReturnPolynomial.eval (cacheEnvironment M B n D) =
      BinaryFraction.powerDenominatorBitBudget n (BinaryFraction.preparedKernelWordBudget M B) D := rfl
  have henv : ∀ i, cacheEnvironment M B n D i ≤ X := by
    intro i
    fin_cases i <;> simp only [cacheEnvironment] <;> assumption
  rw [← heval]
  simpa only [preparedCacheReturnBitDegree] using cacheReturnPolynomial.eval_le_pow _ X hX henv

theorem preparedCachedKernelBitBudget_fixedPower (N M P F exponent eM eF B n D X : ℕ)
    (hX : 2 ≤ X) (hN : Nat.size N ≤ B) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X)
    (he : exponent ≤ X) (htheta : 2 ^ exponent ≤ X) (hword : 16 * B + 200 ≤ X)
    (hscales : 7 + eM + eF ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCartesian : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X)
    (hrepCount : (B + 1) * (64 * F * P + 2) ^ 2 ≤ X)
    (hgroupCount : (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ≤ X)
    (hn : n ≤ X) (hD : D ≤ X) :
    BinaryFraction.preparedKernelBitBudget N M P F exponent eM eF B X +
      BinaryFraction.powerDenominatorBitBudget n (BinaryFraction.preparedKernelWordBudget M B) D + 1 ≤
        X ^ preparedCachedKernelBitDegree := by
  let degree := max preparedKernelBitDegree preparedCacheReturnBitDegree
  have hpositive : 0 < X := by omega
  have hk := (preparedKernelBitBudget_fixedPower N M P F exponent eM eF B X
    hX hN hM hP hF he htheta hword hscales hV hCartesian hrepCount hgroupCount).trans
      (Nat.pow_le_pow_right hpositive (Nat.le_max_left preparedKernelBitDegree preparedCacheReturnBitDegree))
  have hc := (preparedCacheReturnBitBudget_fixedPower M B n D X hX hM (by omega) hn hD).trans
    (Nat.pow_le_pow_right hpositive (Nat.le_max_right preparedKernelBitDegree preparedCacheReturnBitDegree))
  change BinaryFraction.preparedKernelBitBudget N M P F exponent eM eF B X ≤ X ^ degree at hk
  change BinaryFraction.powerDenominatorBitBudget n (BinaryFraction.preparedKernelWordBudget M B) D ≤
    X ^ degree at hc
  have hone : 1 ≤ X ^ degree := Nat.succ_le_of_lt (pow_pos hpositive degree)
  have hfour : 4 ≤ X ^ 2 := (show 4 = (2 : ℕ) ^ 2 by decide).trans_le
    (Nat.pow_le_pow_left hX 2)
  calc
    _ ≤ 2 * X ^ degree + 1 := by omega
    _ ≤ 4 * X ^ degree := by omega
    _ ≤ X ^ 2 * X ^ degree := Nat.mul_le_mul_right _ hfour
    _ = X ^ preparedCachedKernelBitDegree := by
      rw [← pow_add]
      change X ^ (2 + degree) = X ^ (degree + 2)
      rw [Nat.add_comm 2 degree]

namespace BinaryFraction

theorem cachedPreparedLocalKernelWithWork_bounds {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
    (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
    (tau a eta kappa delta : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval target.length → BinaryFraction)
    (old current : Fin M × TargetInterval target.length → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (query : TargetInterval target.length)
    (hb : PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S t
      tau a eta kappa delta parentInitial childMass childInitial old current history integer)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining D V : ℕ)
    (hbaseWidth : base.length ≤ D)
    (hden : (preparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history t draw integer query).1.value.den ∣
        bitWordValue base ^ remaining)
    (hvalue : |(preparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history t draw integer query).1.value| ≤ V) :
    (cachedPreparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history t draw integer query
      base hbase remaining).1.width ≤ Nat.size V + 2 * (remaining * D + 1) + 1 ∧
    (cachedPreparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history t draw integer query
      base hbase remaining).2 ≤ preparedKernelBitBudget N M P F exponent eM eF B S +
        powerDenominatorBitBudget remaining (preparedKernelWordBudget M B) D + 1 := by
  have hk := preparedLocalKernelWithWork_bounds source target parent N P F exponent H Q eM eF B E S
    hP hM hF hPdyadic tau a eta kappa delta parentInitial childMass childInitial old current history t draw integer query hb
  exact finishCachedWithWork_bounds _ base hbase remaining _ D _ V hk.1 hbaseWidth hk.2 hden hvalue

end BinaryFraction

end EditApproximation

end OAI
