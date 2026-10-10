import OAI.Combinatorics.EditApproximation.Geometry.BandActionPolynomial
import OAI.Combinatorics.EditApproximation.Binary.BinarySampledOnlineWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryCoordinateActionWork

namespace OAI

/-! The complete sampled online action, including the triangular search,
coordinate equality tests, final logarithm-gradient and labeled argmax. -/

namespace EditApproximation

private abbrev SP := FiniteBitPolynomial (Fin 5)
private def sampledOnlineOverhead : SP :=
  let M := .input 0
  let v := .input 1
  let d := .input 2
  let K := .input 3
  let B := .input 4
  (K + 1) * (10000 * (B + 3) ^ 2 + 30 * (B + 3)) + M + 2 +
    (v * (5 * M + 3) + (v * M + 1) ^ 2 * (24 * B + 12) + 1) + d +
    v * d * (24 * B + 9) + 2

private def sampledOnlineOverheadEnv (M v d K B : ℕ) : Fin 5 → ℕ
  | 0 => M
  | 1 => v
  | 2 => d
  | 3 => K
  | _ => B

private theorem sampledOnlineOverhead_eval (M v d K B : ℕ) :
    sampledOnlineOverhead.eval (sampledOnlineOverheadEnv M v d K B) =
      triangularChoiceBitBudget K B + M + 2 + BinaryFraction.bandCoordinatesBitBudget M v B + d +
        v * d * (24 * B + 9) + 2 := rfl

def sampledOnlineBitDegree : ℕ := max bandActionBitDegree sampledOnlineOverhead.degree + 1

theorem countedSampledOnlineWithWork_fixedPower {M n : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval n → BinaryFraction) (eta kappa : BinaryFraction)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t B E S : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hS : 2 ≤ S) (hMpos : 0 < M) (hbpos : 0 < b)
    (hM : M ≤ S) (hv : band.length ≤ S) (hd : (listedBandCoordinates band).length ≤ S)
    (hG : G ≤ S) (hK : K ≤ S) (ht : t ≤ S) (hB : B ≤ S) (hE : E ≤ S)
    (hb : Nat.size b ≤ S) (hMb : Nat.size M ≤ B) (hnb : Nat.size n ≤ B)
    (hKb : Nat.size K ≤ B) (hinteger : Nat.size integer.val ≤ B)
    (he : eta.width ≤ B) (hk : kappa.width ≤ B)
    (hi : ∀ i q, (initial i q).width ≤ B)
    (hh : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (hhrange : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
      (table s (i, q)).value ≤ (initial i q).value) :
    (BinaryFraction.countedSampledOnlineWithWork center b initial table eta kappa band hne G K t integer).2 ≤
      S ^ sampledOnlineBitDegree := by
  let d := (listedBandCoordinates band).length
  let j := (triangularChoice K integer).val
  have hj : j ≤ S := (triangularChoice K integer).isLt.le.trans hK
  have ha := bandActionBitBudget_fixedPower
    M d b band.length G j t B B B B E S hS hM hd hb hv hG hj ht hB hB hB hB hE
  have hs := BinaryFraction.sampledOnlineActionWithWork_cost center b initial table eta kappa band hne
    G K t integer B B B B B E hbpos hMpos hKb hinteger he hk
    (fun action _ i => hi i (action i))
    (fun s hs i => hh s hs _ _) heabs hkrange
    (fun s hs i => hhrange s hs _ _)
  have hc := BinaryFraction.countedSampledOnlineWithWork_cost center b initial table eta kappa
    band hne G K t B integer hMb hnb
  have henv : ∀ i, sampledOnlineOverheadEnv M band.length d K B i ≤ S := by
    intro i
    fin_cases i <;> simp only [sampledOnlineOverheadEnv] <;> assumption
  have ho := sampledOnlineOverhead.eval_le_pow _ S hS henv
  rw [sampledOnlineOverhead_eval] at ho
  let D := max bandActionBitDegree sampledOnlineOverhead.degree
  have h1 : S ^ bandActionBitDegree ≤ S ^ D := Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
  have h2 : S ^ sampledOnlineOverhead.degree ≤ S ^ D := Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  change (BinaryFraction.countedSampledOnlineWithWork center b initial table eta kappa band hne G K t integer).2 ≤
    S ^ (D + 1)
  calc
    _ ≤ 2 * S ^ D := by dsimp only [d, j] at ha ho; omega
    _ ≤ S * S ^ D := Nat.mul_le_mul_right _ hS
    _ = _ := (pow_succ' S D).symm

end EditApproximation

end OAI
