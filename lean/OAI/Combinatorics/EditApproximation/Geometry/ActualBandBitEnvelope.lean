import OAI.Combinatorics.EditApproximation.Binary.BinaryActualBandOptimizer
import OAI.Combinatorics.EditApproximation.Numerics.OptimizerBitEnvelope

namespace OAI

/-! A fixed polynomial bounds the complete envelope construction and band
optimizer. In particular the child masses are computed from the initial
table, rather than supplied as already constructed binary fractions. -/

namespace EditApproximation

private theorem square_work_cap (S coefficient width : ℕ) (hc : coefficient ≤ S ^ 2)
    (hw : width ≤ S ^ 2) : coefficient * width ^ 2 ≤ S ^ 6 := by
  calc
    _ ≤ S ^ 2 * (S ^ 2) ^ 2 := Nat.mul_le_mul hc (Nat.pow_le_pow_left hw 2)
    _ = _ := by ring

private theorem square_work_with_constant_cap (S coefficient width extra : ℕ)
    (hS : 64 ≤ S) (hc : coefficient ≤ S ^ 2) (hw : width ≤ S ^ 2)
    (he : extra ≤ S ^ 6) : coefficient * width ^ 2 + extra ≤ S ^ 7 := by
  have h := square_work_cap S coefficient width hc hw
  calc
    _ ≤ 2 * S ^ 6 := by omega
    _ ≤ S * S ^ 6 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

theorem bandEnvelopeBitBudget_le_power (b M vertices B S : ℕ) (hS : 64 ≤ S)
    (hb : Nat.size b ≤ S) (hM : Nat.size M ≤ S) (hv : vertices ≤ S) (hB : B ≤ S) :
    BinaryFraction.bandEnvelopeBitBudget b M vertices B ≤ S ^ 10 := by
  let W := BinaryFraction.bandEnvelopeWordBudget b M B
  have hW : W ≤ 3 * S + 8 := by
    dsimp only [W, BinaryFraction.bandEnvelopeWordBudget]
    omega
  have hW1 : W + 1 ≤ S ^ 2 := by nlinarith
  have hW3 : 3 * W + 2 ≤ S ^ 2 := by nlinarith
  have hW2 : 2 * W ≤ S ^ 2 := by nlinarith
  have htail : 3 * W + 6 ≤ S ^ 2 := by nlinarith
  have hfloor : Nat.size b + Nat.size M + 6 ≤ S ^ 2 := by nlinarith
  have h1000 : 1000 ≤ S ^ 2 := by nlinarith
  have h2100 : 2100 ≤ S ^ 2 := by nlinarith
  have hpos : 0 < S := by omega
  have hpow6 : 2 ≤ S ^ 6 := (by omega : 2 ≤ S).trans (Nat.le_pow (by omega))
  have hfc := square_work_cap S 2100 (Nat.size b + Nat.size M + 6) h2100 hfloor
  have hcmp := square_work_with_constant_cap S 1000 (W + 1) 2 hS h1000 hW1 hpow6
  have hbig := square_work_with_constant_cap S 1000 (3 * W + 2) 2 hS h1000 hW3 hpow6
  have hmember : vertices * (1000 * (W + 1) ^ 2 + 2) ≤ S ^ 8 := by
    calc
      _ ≤ S * S ^ 7 := Nat.mul_le_mul hv hcmp
      _ = _ := by ring
  have hscan : 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) ≤ S ^ 9 := by
    calc
      _ ≤ S ^ 2 * S ^ 7 := Nat.mul_le_mul hW2 hbig
      _ = _ := by ring
  have h6 : S ^ 6 ≤ S ^ 9 := Nat.pow_le_pow_right hpos (by omega)
  have h7 : S ^ 7 ≤ S ^ 9 := Nat.pow_le_pow_right hpos (by omega)
  have h8 : S ^ 8 ≤ S ^ 9 := Nat.pow_le_pow_right hpos (by omega)
  have h2 : S ^ 2 ≤ S ^ 9 := Nat.pow_le_pow_right hpos (by omega)
  have hsmall : vertices + 6 ≤ S ^ 9 := by
    have hsq : S + 6 ≤ S ^ 2 := by nlinarith
    omega
  change 2100 * (Nat.size b + Nat.size M + 6) ^ 2 +
      (1 + vertices * (1000 * (W + 1) ^ 2 + 2)) + (1000 * (W + 1) ^ 2 + 1) +
      (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + vertices + 4 ≤ _
  have hten : S ^ 10 = S * S ^ 9 := by ring
  calc
    _ ≤ 6 * S ^ 9 := by
      nlinarith only [hfc, hcmp, hmember, hscan, htail, h6, h7, h8, h2, hsmall]
    _ ≤ S * S ^ 9 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := hten.symm

def actualBandOptimizerBitDegree : ℕ := max 12 (2 * preparedOptimizerBitPolynomialDegree) + 2

theorem actualBandOptimizerBitBudget_le_fixed_power
    (M d b vertices G K t Be Bk Bi Bt E S : ℕ) (hS : 64 ≤ S)
    (hM : M ≤ S) (hd : d ≤ S) (hb : Nat.size b ≤ S) (hv : vertices ≤ S)
    (hG : G ≤ S) (hK : K ≤ S) (ht : t ≤ S)
    (hBe : Be ≤ S) (hBk : Bk ≤ S) (hBi : Bi ≤ S) (hBt : Bt ≤ S) (hE : E ≤ S) :
    BinaryFraction.actualBandOptimizerBitBudget M d b vertices G K t Be Bk Bi Bt E ≤
      S ^ actualBandOptimizerBitDegree := by
  have hpos : 0 < S := by omega
  have hSsq : S ≤ S ^ 2 := Nat.le_pow (by omega)
  have hMbits : Nat.size M ≤ S := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hM
  have hmass : 3 * BinaryFraction.bandEnvelopeWordBudget b M Bi + 1 ≤ S ^ 2 := by
    unfold BinaryFraction.bandEnvelopeWordBudget
    nlinarith
  have hprepared := preparedBandOptimizerBitBudget_le_fixed_power
    M d vertices G K t Be Bk (3 * BinaryFraction.bandEnvelopeWordBudget b M Bi + 1) Bt E
    (S ^ 2) ((by omega : 2 ≤ S).trans hSsq)
    (hM.trans hSsq) (hd.trans hSsq) (hv.trans hSsq) (hG.trans hSsq) (hK.trans hSsq)
    (ht.trans hSsq) (hBe.trans hSsq) (hBk.trans hSsq) hmass (hBt.trans hSsq) (hE.trans hSsq)
  rw [← pow_mul] at hprepared
  have henv := bandEnvelopeBitBudget_le_power b M vertices Bi S hS hb hMbits hv hBi
  have h6 : 6 ≤ S ^ 10 := (by omega : 6 ≤ S).trans (Nat.le_pow (by omega))
  have henvelope : M * (BinaryFraction.bandEnvelopeBitBudget b M vertices Bi + 6) ≤ S ^ 12 := by
    calc
      _ ≤ S * (S ^ 10 + 6) := Nat.mul_le_mul hM (by omega)
      _ ≤ S * (S * S ^ 10) := Nat.mul_le_mul_left S (by
        calc
          _ ≤ 2 * S ^ 10 := by omega
          _ ≤ S * S ^ 10 := Nat.mul_le_mul_right _ (by omega))
      _ = _ := by ring
  let D := max 12 (2 * preparedOptimizerBitPolynomialDegree)
  have hleft : S ^ 12 ≤ S ^ D := Nat.pow_le_pow_right hpos (Nat.le_max_left _ _)
  have hright : S ^ (2 * preparedOptimizerBitPolynomialDegree) ≤ S ^ D :=
    Nat.pow_le_pow_right hpos (Nat.le_max_right _ _)
  have hone : 1 ≤ S ^ D := Nat.one_le_pow _ _ hpos
  change M * (BinaryFraction.bandEnvelopeBitBudget b M vertices Bi + 6) +
      BinaryFraction.preparedBandOptimizerBitBudget M d vertices G K t Be Bk
        (3 * BinaryFraction.bandEnvelopeWordBudget b M Bi + 1) Bt E + 1 ≤ S ^ (D + 2)
  calc
    _ ≤ 3 * S ^ D := by omega
    _ ≤ S ^ D * S ^ 2 := by
      simpa only [Nat.mul_comm] using
        Nat.mul_le_mul_right (S ^ D) (show 3 ≤ S ^ 2 by nlinarith)
    _ = _ := (pow_add S D 2).symm

end EditApproximation

end OAI
