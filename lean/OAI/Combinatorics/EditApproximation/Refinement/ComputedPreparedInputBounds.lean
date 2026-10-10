import OAI.Combinatorics.EditApproximation.Refinement.PhysicalPreparedInputBounds
import OAI.Combinatorics.EditApproximation.Refinement.ComputedParameterRegisters
import OAI.Combinatorics.EditApproximation.Refinement.ComputedNumericalParameters

namespace OAI

namespace EditApproximation
open Filter

private theorem precision_power_bound (p : ℕ) : p + 20 ≤ 8000 * (p + 1) := by omega

private theorem prepared_loop_caps (H M P p : ℕ) (hH : 64 ≤ H)
    (hM : M ≤ H) (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    (40 * P + 2) ^ (2 * M) ≤ H ^ ((100 * M + 100000) * (p + 1)) ∧
    ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ H ^ ((100 * M + 100000) * (p + 1)) ∧
    (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ H ^ ((100 * M + 100000) * (p + 1)) := by
  have hHp : 0 < H := by omega
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul (by nlinarith only [hH]) hPcap
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hbase : (40 * P + 2) ^ 2 + 1 ≤ H ^ (2 * (p + 22) + 1) := by
    have hs := Nat.pow_le_pow_left hbox 2
    have hunit : 1 ≤ (H ^ (p + 22)) ^ 2 := one_le_pow₀ (one_le_pow₀ (by omega))
    calc
      _ ≤ 2 * (H ^ (p + 22)) ^ 2 := by omega
      _ ≤ H * (H ^ (p + 22)) ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [← pow_mul, ← pow_succ']; congr 1; omega
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (H ^ (p + 22)) ^ (2 * M) := Nat.pow_le_pow_left hbox _
      _ = H ^ ((p + 22) * (2 * M)) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHp (by nlinarith only [Nat.zero_le (M * p), Nat.zero_le p, Nat.zero_le M])
  · calc
      _ ≤ (H ^ (2 * (p + 22) + 1)) ^ (M + 1) := Nat.pow_le_pow_left hbase _
      _ = H ^ ((2 * (p + 22) + 1) * (M + 1)) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHp (by nlinarith only [Nat.zero_le (M * p), Nat.zero_le p, Nat.zero_le M])
  · have hg := optimizer_parameter_budget_le H M P p hH hM hP hPcap
    calc
      _ ≤ (H ^ (2 * p + 46)) ^ 80 := Nat.pow_le_pow_left (by omega) 80
      _ = H ^ ((2 * p + 46) * 80) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHp (by nlinarith only [Nat.zero_le (M * p), Nat.zero_le p, Nat.zero_le M])

/-- Every numeric premise of the prepared kernel follows from the computed
parameters. Width assumptions here concern only the five actual parameter
words; cached data are added by `physicalPreparedStep_inputBounds`. -/
theorem computedPreparedNumericBounds :
    ∀ᶠ N : ℕ in atTop, ∀ nx ny : ℕ, nx + ny ≤ N → ∀ t : ℕ, t ≤ inputHeight N ^ 2 →
      ∀ tau a eta kappa delta : BinaryFraction,
      tau.width ≤ inputHeight N ^ 8 → a.width ≤ inputHeight N ^ 8 →
      eta.width ≤ inputHeight N ^ 8 → kappa.width ≤ inputHeight N ^ 8 →
      delta.width ≤ inputHeight N ^ 8 → |eta.value| ≤ ((inputHeight N ^ 5 : ℕ) : ℚ) →
      (0 ≤ kappa.value ∧ kappa.value ≤ 1) →
      ∀ integer : ℕ → TargetInterval ny → ℕ,
      (∀ b r, Nat.size (integer b r) ≤ inputHeight N) →
      BinaryFraction.PreparedKernelNumericBounds (nx := nx) (M := (integerParameters N).M)
        N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8) (inputHeight N ^ 5)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t tau a eta kappa delta integer := by
  filter_upwards [computedParameterPower_word,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hpower hell
  intro nx ny hsize t ht tau a eta kappa delta htau ha heta hk hd hrate hkRange integer hint
  let H := inputHeight N
  let p := coarseExponent (inputSmallLog N)
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let L := (100 * M + 100000) * (p + 1)
  have hpowers : ∀ k : ℕ, k ≤ 8000 * (p + 1) → Nat.size (H ^ k) ≤ H := hpower
  change BinaryFraction.PreparedKernelNumericBounds (nx := nx) (M := M)
    N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (H ^ 8) (H ^ 5) (H ^ L) t
    tau a eta kappa delta integer
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hHp : 0 < H := by omega
  have hM : M ≤ H := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  have hP : 1 ≤ P := one_le_pow₀ (by omega)
  have hPcap : P ≤ H ^ (p + 20) := le_rfl
  have hH8 : H ^ 2 ≤ H ^ 8 := Nat.pow_le_pow_right hHp (by decide)
  have hsmall : H + 2 ≤ H ^ 8 := (by nlinarith only [hH] : H + 2 ≤ H ^ 2).trans hH8
  have hHle : H ≤ H ^ 8 := by omega
  have hL : p + 20 ≤ L := by dsimp only [L]; nlinarith only [Nat.zero_le (M * p), Nat.zero_le M, Nat.zero_le p]
  have hL20 : 20 ≤ L := (Nat.le_add_left 20 p).trans hL
  have hHL : H ≤ H ^ L := Nat.le_pow (by omega)
  have hsizeN : Nat.size N ≤ H := computed_input_size_le_height N
  have hMF : Nat.size M ≤ H := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hM
  have hF : Nat.size (inputSmallLog N) ≤ H :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
  have hPs : Nat.size P ≤ H := by
    change Nat.size (H ^ (p + 20)) ≤ H
    exact hpowers (p + 20) (precision_power_bound p)
  have hQs : Nat.size (inputSmallLog N ^ 80) ≤ H :=
    (Nat.size_le_size (Nat.pow_le_pow_left (computed_smallLog_le_height N) 80)).trans
      (hpowers 80 (by omega))
  have he : smallLogExponent N ≤ H :=
    (Nat.lt_two_pow_self.le : smallLogExponent N ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have htheta : 40 * smallLogExponent N + 1 ≤ H ^ 8 :=
    (by nlinarith only [he, hH] : 40 * smallLogExponent N + 1 ≤ H ^ 2).trans hH8
  have hscale : heightExponent N / 20 + smallLogExponent N + 7 ≤ H ^ 8 := by
    have heM : heightExponent N / 20 ≤ H :=
      (Nat.div_le_self _ _).trans Nat.lt_two_pow_self.le
    exact (by nlinarith only [heM, he, hH] :
      heightExponent N / 20 + smallLogExponent N + 7 ≤ H ^ 2).trans hH8
  have hcoord : Nat.size (M * (40 * P + 2) ^ 2) ≤ H :=
    (Nat.size_le_size (wide_coordinate_budget_le H M P p hH hM hP hPcap)).trans
      (hpowers (2 * p + 45) (by omega))
  have hiter : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ H := by
    have hg := optimizer_parameter_budget_le H M P p hH hM hP hPcap
    have hi : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ H ^ ((2 * p + 46) * 80) := by
      calc
        _ ≤ (H ^ (2 * p + 46)) ^ 80 := Nat.pow_le_pow_left (by omega) 80
        _ = _ := (pow_mul H _ _).symm
    exact (Nat.size_le_size hi).trans (hpowers ((2 * p + 46) * 80) (by omega))
  have hcaps := prepared_loop_caps H M P p hH hM hP hPcap
  have hword : 3 * (H ^ 8 + 4) + 4 ≤ H ^ L := by
    have hunit : 1 ≤ H ^ 8 := one_le_pow₀ (by omega)
    calc
      _ ≤ 19 * H ^ 8 := by omega
      _ ≤ H ^ 2 * H ^ 8 := Nat.mul_le_mul_right _ (by nlinarith only [hH])
      _ = H ^ 10 := by rw [← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right hHp (by omega)
  refine {
    largeBits := (by nlinarith only [hH] : 10 ≤ H ^ 2).trans hH8
    inputSize := hsizeN.trans hHle
    sourceSize := (Nat.add_le_add_right (Nat.size_le_size (show nx ≤ N by omega) |>.trans hsizeN) 2).trans hsmall
    targetSize := (Nat.add_le_add_right (Nat.size_le_size (show ny ≤ N by omega) |>.trans hsizeN) 2).trans hsmall
    aritySize := (Nat.add_le_add_right hMF 2).trans hsmall
    precisionSize := hPs.trans hHle
    factorSize := (Nat.add_le_add_right hF 2).trans hsmall
    sampleSize := (Nat.add_le_add_right hQs 2).trans hsmall
    thetaSize := htheta
    scaleSizes := hscale
    heightSize := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hHle
    coordinateSize := hcoord.trans hHle
    iterationSize := hiter.trans hHle
    drawSize := fun b r => (hint b r).trans hHle
    tauSize := htau
    factorWidth := ha
    rateSize := heta
    optimismSize := hk
    decrementSize := hd
    rateMagnitude := hrate
    optimismRange := hkRange
    scalePositive := ?_
    arityCap := hM.trans ?_
    precisionCap := hPcap.trans (Nat.pow_le_pow_right hHp hL)
    rateCap := Nat.pow_le_pow_right hHp (by omega)
    timeCap := ht.trans (Nat.pow_le_pow_right hHp (by omega))
    wordCap := hword
    actionCap := hcaps.1
    cartesianCap := hcaps.2.1
    iterationCap := hcaps.2.2 }
  · exact (by omega : 2 ≤ H).trans hHL
  · exact hHL

end EditApproximation

end OAI
