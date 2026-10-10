import OAI.Combinatorics.EditApproximation.Geometry.WarmupReadWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedRefinementReadBudget

namespace OAI

/-! A polynomial earlier-edge bound for the complete charged warmup
query. It includes all preceding-pass copy reads and pass-zero coarse
reads used by its initial cones. -/

namespace EditApproximation

def warmupReadBudget (scales window P F Amax M copies : ℕ) : ℕ :=
  (1 + window * (64 * F * P + 2) ^ 2) *
    ((1 + scales * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies) +
    window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2

theorem warmupReadBudget_box (Z scales window P F Amax M copies : ℕ)
    (hZ : 64 ≤ Z) (hscales : scales ≤ Z) (hwindow : window ≤ Z)
    (hP : P ≤ Z) (hF : F ≤ Z) (hA : Amax ≤ Z) (hM : M ≤ Z)
    (hcopies : copies ≤ Z) : warmupReadBudget scales window P F Amax M copies ≤ Z ^ 24 := by
  have hZone : 1 ≤ Z := by omega
  have hZtwo : 2 ≤ Z := by omega
  have hbase (c x : ℕ) (hc : c ≤ Z) (hx : 2 ≤ x) : c * x + 2 ≤ Z ^ 2 * x := by
    have hcx := Nat.mul_le_mul_right x hc
    have hzx : 2 ≤ Z * x := hx.trans (Nat.le_mul_of_pos_left x hZone)
    have hcoeff := Nat.mul_le_mul_right x (show 2 * Z ≤ Z ^ 2 by nlinarith only [hZtwo])
    nlinarith only [hcx, hzx, hcoeff]
  have hadd (k : ℕ) : 1 + Z ^ k ≤ Z ^ (k + 1) := by
    have hp : 1 ≤ Z ^ k := one_le_pow₀ hZone
    have hm := Nat.mul_le_mul_right (Z ^ k) hZtwo
    rw [pow_succ]
    nlinarith only [hp, hm]
  have h64 : 64 ≤ Z := hZ
  have h40 : 40 ≤ Z := by omega
  have hsmall : 64 * F * P + 2 ≤ Z ^ 4 := by
    calc
      _ ≤ 64 * Z * Z + 2 := Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 64 hF) hP) 2
      _ ≤ _ := by
        convert hbase 64 (Z ^ 2) h64 ((Nat.pow_le_pow_left hZtwo 2).trans' (by norm_num)) using 1 <;> ring
  have hinitialBase : 64 * Amax ^ 2 * P + 2 ≤ Z ^ 5 := by
    calc
      _ ≤ 64 * Z ^ 2 * Z + 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hA 2)) hP) 2
      _ ≤ _ := by
        convert hbase 64 (Z ^ 3) h64 ((Nat.pow_le_pow_left hZtwo 3).trans' (by norm_num)) using 1 <;> ring
  have hwideBase : 40 * P + 2 ≤ Z ^ 3 := by
    calc
      _ ≤ 40 * Z + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left 40 hP) 2
      _ ≤ _ := by convert hbase 40 Z h40 hZtwo using 1; ring
  have hraw : window * (64 * F * P + 2) ^ 2 ≤ Z ^ 9 := by
    exact (Nat.mul_le_mul hwindow (Nat.pow_le_pow_left hsmall 2)).trans_eq (by ring)
  have hrawInitial : scales * (64 * Amax ^ 2 * P + 2) ^ 2 ≤ Z ^ 11 := by
    exact (Nat.mul_le_mul hscales (Nat.pow_le_pow_left hinitialBase 2)).trans_eq (by ring)
  have hinit : (1 + scales * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies ≤ Z ^ 13 := by
    exact (Nat.mul_le_mul ((Nat.add_le_add_left hrawInitial 1).trans (hadd 11))
      (max_le hZone hcopies)).trans_eq (by ring)
  have hfirst : (1 + window * (64 * F * P + 2) ^ 2) *
      ((1 + scales * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies) ≤ Z ^ 23 := by
    exact (Nat.mul_le_mul ((Nat.add_le_add_left hraw 1).trans (hadd 9)) hinit).trans_eq (by ring)
  have hsecond : window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 ≤ Z ^ 23 := by
    calc
      _ ≤ Z ^ 9 * Z * (Z ^ 3) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul hraw hM) (Nat.pow_le_pow_left hwideBase 2)
      _ = Z ^ 16 := by ring
      _ ≤ _ := pow_le_pow_right₀ hZone (by decide)
  exact (Nat.add_le_add hfirst hsecond).trans (by
    have hm := Nat.mul_le_mul_right (Z ^ 23) hZtwo
    have heq : Z ^ 24 = Z ^ 23 * Z := pow_succ Z 23
    calc
      Z ^ 23 + Z ^ 23 = 2 * Z ^ 23 := (two_mul _).symm
      _ ≤ Z * Z ^ 23 := hm
      _ = Z ^ 24 := by rw [heq]; exact Nat.mul_comm _ _)

theorem computed_dyadicScales_length (N : ℕ) (hH : 2 ≤ inputHeight N) :
    (dyadicScales N).length ≤ inputHeight N ^ 2 := by
  have hlog : Nat.log 2 N ≤ inputHeight N := by
    apply (Nat.log_le_clog 2 N).trans
    apply (Nat.clog_mono_right 2 (Nat.le_add_right N 2)).trans
    exact Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (Nat.clog 2 (N + 2))
  simp only [dyadicScales, List.length_map, List.length_range]
  nlinarith only [hlog, hH]

theorem computed_warmupReadBudget_le (N M P copies : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
    (hP : P = (integerParameters N).P) (hcopies : copies ≤ inputHeight N ^ 2) :
    warmupReadBudget (dyadicScales N).length (computedSeedInitialExponent N + 8)
      P (inputSmallLog N) (integerParameters N).initialFactor M copies ≤
      inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)) := by
  let H := inputHeight N
  let p := coarseExponent (inputSmallLog N)
  let Z := H ^ (p + 20)
  have hF := computed_smallLog_le_height N
  have hH : 64 ≤ H := (by omega : 64 ≤ inputSmallLog N).trans hF
  have hZone : 1 ≤ H := by omega
  have hHZ : H ≤ Z := by
    calc
      H = H ^ 1 := (pow_one H).symm
      _ ≤ H ^ (p + 20) := pow_le_pow_right₀ hZone (by omega)
  have hH2Z : H ^ 2 ≤ Z := pow_le_pow_right₀ hZone (by omega)
  have hH3Z : H ^ 3 ≤ Z := pow_le_pow_right₀ hZone (by omega)
  have hscales : (dyadicScales N).length ≤ Z := (computed_dyadicScales_length N (by omega)).trans hH2Z
  have hwindow : computedSeedInitialExponent N + 8 ≤ Z :=
    (computed_window_le_height_cube N hN (by omega) (by omega)).trans hH3Z
  have hPZ : P ≤ Z := by change P ≤ (integerParameters N).P; exact hP.le
  have hAZ : (integerParameters N).initialFactor ≤ Z :=
    pow_le_pow_right₀ hZone (by omega)
  have hMZ : M ≤ Z := by
    rw [hM]
    exact (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)).trans hHZ
  have hbound := warmupReadBudget_box Z (dyadicScales N).length (computedSeedInitialExponent N + 8)
    P (inputSmallLog N) (integerParameters N).initialFactor M copies (hH.trans hHZ)
    hscales hwindow hPZ (hF.trans hHZ) hAZ hMZ (hcopies.trans hH2Z)
  apply hbound.trans
  dsimp only [Z]
  rw [← pow_mul]
  exact pow_le_pow_right₀ hZone (by dsimp only [p]; omega)

theorem computed_chargedWarmupQuery_reads {α : Type*} [DecidableEq α]
    {M J passes copies T S : ℕ} (source target : List α) (N P : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
    (hcopies : copies ≤ inputHeight N ^ 2) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (oracle) (hA : 1 ≤ factor parent.val.pass)
    (hAmax : factor parent.val.pass ≤ ((integerParameters N).initialFactor : ℚ)) :
    (chargedWarmupQuery source target N P (inputSmallLog N) factor multiplier parent).cost
      oracle (fun _ => 1) ≤ inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)) := by
  have hPpos : 0 < P := by
    rw [hP]
    change 0 < inputHeight N ^ _
    exact pow_pos (Nat.two_pow_pos _) _
  exact (chargedWarmupQuery_cost_le source target N P (inputSmallLog N)
    (integerParameters N).initialFactor (computedSeedInitialExponent N + 8) factor multiplier parent oracle
    hPpos (by omega) hA hAmax (fun w => computed_refinement_window N hN (by omega)
      (factor parent.val.pass) w hAmax)).trans
      (computed_warmupReadBudget_le N M P copies hN hell hM hP hcopies)

theorem computed_chargedInitialQuery_reads {α : Type*} [DecidableEq α]
    {M J passes copies T S : ℕ} (source target : List α) (N P : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
    (hcopies : copies ≤ inputHeight N ^ 2) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (oracle) (hA : 1 ≤ factor parent.val.pass)
    (hAmax : factor parent.val.pass ≤ ((integerParameters N).initialFactor : ℚ)) :
    (physicalInitialQuery source target N P (inputSmallLog N) (factor parent.val.pass)
      (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)).cost oracle (fun _ => 1) ≤
      inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)) := by
  have hPpos : 0 < P := by
    rw [hP]
    change 0 < inputHeight N ^ _
    exact pow_pos (Nat.two_pow_pos _) _
  let initialCost := (1 + (dyadicScales N).length *
    (64 * (integerParameters N).initialFactor ^ 2 * P + 2) ^ 2) * max 1 copies
  have hi : (physicalInitialQuery source target N P (inputSmallLog N) (factor parent.val.pass)
      (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)).cost oracle (fun _ => 1) ≤
      initialCost :=
    physicalInitialQuery_cost_le source target N P (inputSmallLog N) (integerParameters N).initialFactor
      (max 1 copies) _ _ _ _ oracle hPpos hA hAmax
      (fun r => chargedSeedQuery_cost_le N multiplier parent _ oracle)
  have hb : initialCost ≤ warmupReadBudget (dyadicScales N).length
      (computedSeedInitialExponent N + 8) P (inputSmallLog N) (integerParameters N).initialFactor M copies := by
    exact (Nat.le_mul_of_pos_left initialCost (by omega)).trans (Nat.le_add_right _ _)
  exact hi.trans (hb.trans (computed_warmupReadBudget_le N M P copies hN hell hM hP hcopies))

end EditApproximation

end OAI
