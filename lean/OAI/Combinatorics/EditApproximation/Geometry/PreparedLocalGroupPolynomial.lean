import OAI.Combinatorics.EditApproximation.Geometry.PreparedGroupPolynomial
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalGroupWork

namespace OAI

/-! A fixed-degree cap on all whole-cell loops at a query. Distance scales
enter through their bit length; their numeric size is never charged. -/

namespace EditApproximation

private abbrev LP := FiniteBitPolynomial (Fin 8)
private def lpGuard (B : LP) : LP :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8
private def lpCellSetup (B : LP) : LP :=
  100 * (B + 1) + 4200 * (B + 6) ^ 2 + 400 * (4 * B + 21) ^ 2 + 100 * (4 * B + 25)
private def lpTargetCells (K B : LP) : LP := 2 * lpCellSetup B + K + K + K * (5 * K + 3) + 2
private def lpScales (eM eF B : LP) : LP :=
  (7 + eM + eF) * (eM + B + eF + 13) + .bitLength eM + .bitLength B + .bitLength eF + 8
private def localGroupPolynomial : LP :=
  let F := .input 0
  let thetaPow := .input 1
  let B := .input 2
  let eM := .input 3
  let eF := .input 4
  let X := .input 5
  let K := (32 * F + 2) * thetaPow + 2
  let scale := 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 + lpTargetCells K (4 * B + 40) +
    K ^ 2 * (lpScales eM eF B + X ^ preparedCellGroupBitDegree + 4) + B + 4
  (B + 1) * (lpGuard (B + 3) + scale + B + 4 + K ^ 2 + 3) + (B + 1) + B + 2

def preparedLocalGroupBitDegree : ℕ := localGroupPolynomial.degree

private def localGroupEnvironment (F thetaPow B eM eF X : ℕ) : Fin 8 → ℕ
  | 0 => F
  | 1 => thetaPow
  | 2 => B
  | 3 => eM
  | 4 => eF
  | 5 => X
  | _ => 0

private def localGroupMajorant (F thetaPow B eM eF X : ℕ) : ℕ :=
  let K := (32 * F + 2) * thetaPow + 2
  let scale := 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
    BinaryFraction.targetCellsBitBudget K K (4 * B + 40) +
    K ^ 2 * (BinaryFraction.groupScalesBitBudget eM B eF + X ^ preparedCellGroupBitDegree + 4) + B + 4
  (B + 1) * (BinaryFraction.localEligibilityBitBudget (B + 3) + scale + B + 4 + K ^ 2 + 3) +
    (B + 1) + B + 2

private theorem localGroupPolynomial_eval (F thetaPow B eM eF X : ℕ) :
    localGroupPolynomial.eval (localGroupEnvironment F thetaPow B eM eF X) =
      localGroupMajorant F thetaPow B eM eF X := rfl

theorem preparedLocalGroupsBitBudget_fixedPower (N M P F exponent eM eF B X : ℕ)
    (hX : 2 ≤ X) (hN : Nat.size N ≤ B) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X)
    (he : exponent ≤ X) (htheta : 2 ^ exponent ≤ X) (hword : 16 * B + 200 ≤ X)
    (hscales : 7 + eM + eF ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCartesian : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.preparedLocalGroupsBitBudget N M P F exponent eM eF B ≤
      X ^ preparedLocalGroupBitDegree := by
  let count := max 1 N.bits.length
  let K := (32 * F + 2) * 2 ^ exponent + 2
  let scale := 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
    BinaryFraction.targetCellsBitBudget K K (4 * B + 40) +
    K ^ 2 * (BinaryFraction.groupScalesBitBudget eM B eF + X ^ preparedCellGroupBitDegree + 4) + B + 4
  let cost := BinaryFraction.localEligibilityBitBudget (B + 3) + scale + B + 4 + K ^ 2 + 3
  have hcount : count ≤ B + 1 := by dsimp only [count]; rw [Nat.size_eq_bits_len]; omega
  have hscale (eb : ℕ) (heb : eb ∈ List.range count) :
      BinaryFraction.preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B ≤ scale := by
    have heB : eb ≤ B := by have := List.mem_range.mp heb; omega
    have hbb : Nat.size (2 ^ eb) ≤ X := by rw [Nat.size_pow]; omega
    have hc := preparedCellGroupBitBudget_fixedPower M (7 + eM + eF) exponent (2 ^ eb) P (16 * B + 200) X
      hX hM hscales he hbb hP hword hV hCartesian
    have hs : BinaryFraction.groupScalesBitBudget eM eb eF ≤
        BinaryFraction.groupScalesBitBudget eM B eF := by
      unfold BinaryFraction.groupScalesBitBudget
      gcongr
      exact Nat.size_le_size heB
    unfold BinaryFraction.preparedLocalGroupScaleBitBudget
    change 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
      BinaryFraction.targetCellsBitBudget K K (4 * B + 40) + K ^ 2 *
        (BinaryFraction.groupScalesBitBudget eM eb eF +
          BinaryFraction.preparedCellGroupBitBudget M (7 + eM + eF) exponent (2 ^ eb) P (16 * B + 200) + 4) + eb + 4 ≤ _
    dsimp only [scale]
    gcongr
  have hsum : ((List.range count).map fun eb => BinaryFraction.localEligibilityBitBudget (B + 3) +
      BinaryFraction.preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 + K ^ 2 + 3).sum ≤
        count * cost := by
    have hh := List.sum_le_sum (l := List.range count)
      (f := fun eb : ℕ => BinaryFraction.localEligibilityBitBudget (B + 3) +
        BinaryFraction.preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 + K ^ 2 + 3)
      (g := fun _ => cost) (by
      intro eb heb
      have heB : eb ≤ B := by have := List.mem_range.mp heb; omega
      have hs := hscale eb heb
      dsimp only [cost]
      omega)
    simpa [List.map_const', List.length_range, List.sum_replicate, nsmul_eq_mul] using hh
  have hmajor : BinaryFraction.preparedLocalGroupsBitBudget N M P F exponent eM eF B ≤
      localGroupMajorant F (2 ^ exponent) B eM eF X := by
    have hh := hsum.trans (Nat.mul_le_mul_right cost hcount)
    unfold BinaryFraction.preparedLocalGroupsBitBudget
    change ((List.range count).map fun eb : ℕ => BinaryFraction.localEligibilityBitBudget (B + 3) +
      BinaryFraction.preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 + K ^ 2 + 3).sum +
      count + N.bits.length + 2 ≤ _
    unfold localGroupMajorant
    change _ ≤ (B + 1) * cost + (B + 1) + B + 2
    have hNbits : N.bits.length ≤ B := by simpa only [Nat.size_eq_bits_len] using hN
    omega
  have henv : ∀ i, localGroupEnvironment F (2 ^ exponent) B eM eF X i ≤ X := by
    intro i
    fin_cases i <;> simp [localGroupEnvironment] <;> omega
  exact hmajor.trans (by
    rw [← localGroupPolynomial_eval]
    exact localGroupPolynomial.eval_le_pow _ X hX henv)

end EditApproximation

end OAI
