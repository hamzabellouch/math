import OAI.Combinatorics.EditApproximation.Coarse.CoarsePrecision
import OAI.Combinatorics.EditApproximation.Coarse.CoarseGlobalSeed
import OAI.Combinatorics.EditApproximation.Refinement.ComputedParameterRegisters

namespace OAI

namespace EditApproximation
open Filter

private theorem coarseEncoding_scalar (H B D q L n k : ℕ)
    (hH : 100 ≤ H) (hB : 2 ≤ B) (hD : D ≤ H)
    (hb : Nat.size B ≤ 2 * H) (hq : Nat.size q ≤ 2 * H)
    (hL : Nat.size L ≤ 2 * H) (hn : Nat.size n ≤ 2 * H) (hk : Nat.size k ≤ 2 * H) :
    Nat.size (n + B * k * coarseInternalNodes B D) +
      2 * (Nat.size q + D * (Nat.size L + Nat.size B + Nat.size q) + 2) + 1 ≤ H ^ 3 := by
  have hnodes := (Nat.size_le_size (show coarseInternalNodes B D ≤ B ^ D from
    Nat.le_of_succ_le (coarseInternalNodes_add_one_le_pow B D hB))).trans
    (natural_power_bit_length B D)
  have hprod := natural_product_bit_length (B * k) (coarseInternalNodes B D)
  have hbk := natural_product_bit_length B k
  have hsum := natural_sum_bit_length n (B * k * coarseInternalNodes B D)
  have hdh := Nat.mul_le_mul hD hb
  have hsuminputs : Nat.size L + Nat.size B + Nat.size q ≤ 6 * H := by omega
  have hcoeff := Nat.mul_le_mul hD hsuminputs
  have hhsq : H ≤ H ^ 2 := Nat.le_pow (by decide)
  have hcub : 100 * H ^ 2 ≤ H ^ 3 := by
    have hh := Nat.mul_le_mul_right (H ^ 2) hH
    nlinarith only [hh]
  nlinarith only [hnodes, hprod, hbk, hsum, hdh, hcoeff, hb, hq, hL, hn, hk,
    hH, hhsq, hcub]

/-- Every root cell of every computed coarse call has polynomial bit width,
without conditioning on the accuracy event or on its threshold labels. -/
 theorem computedCoarse_root_encoding_bits :
    ∀ᶠ N : ℕ in atTop, ∀ B d n k : ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N n →
      n ≤ N → k ≤ 2 * (N + 2) →
      ∀ {α : Type} [DecidableEq α] (frame : List (Option α))
        (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d),
        tree.word.length ≤ N → ∀ start shift,
      rationalEncodingBits (coarseThresholdEstimate k (initialThresholdQ N) (initialLambda N)
        frame tree draws k start shift) ≤ inputHeight N ^ 3 := by
  filter_upwards [computedParameterPower_word, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hpower hN hell
  intro B d n k hBdef hddef hn hk α inst frame tree draws htree start shift
  have hH := computed_coarse_height_large N (by omega) hell
  have hbranch := computed_coarse_branching N (by omega) hell
  have hB : 0 < B := by omega
  have hq : 0 < inputHeight N ^ 4 := pow_pos (Nat.two_pow_pos _) _
  have hL : 0 < 64 * inputHeight N := Nat.mul_pos (by decide) (Nat.two_pow_pos _)
  have hraw := coarseThresholdEstimate_encoding_bits k (inputHeight N ^ 4)
    (64 * inputHeight N) frame tree draws hB hq hL start shift
  have hbSize : Nat.size B ≤ 2 * inputHeight N := by
    have hb := Nat.size_le_size (computed_coarse_B_upper N (by omega) hell)
    simp only [Nat.size_pow] at hb
    rw [hBdef]
    omega
  have hqSize : Nat.size (inputHeight N ^ 4) ≤ 2 * inputHeight N := by
    have h := hpower 4 (by omega)
    omega
  have hHSize : Nat.size (inputHeight N) ≤ inputHeight N :=
    Nat.size_le.mpr (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))
  have hLSize : Nat.size (64 * inputHeight N) ≤ 2 * inputHeight N := by
    have h := natural_product_bit_length 64 (inputHeight N)
    rw [show Nat.size 64 = 7 by decide] at h
    omega
  have hnSize : Nat.size tree.word.length ≤ 2 * inputHeight N := by
    have h := (Nat.size_le_size (htree.trans (Nat.le_add_right N 2))).trans (inputLength_register_word N)
    omega
  have hkSize : Nat.size k ≤ 2 * inputHeight N := by
    have h := (Nat.size_le_size hk).trans (natural_product_bit_length 2 (N + 2))
    have hn := inputLength_register_word N
    rw [show Nat.size 2 = 2 by decide] at h
    omega
  have hscalar := coarseEncoding_scalar (inputHeight N) B d
    (inputHeight N ^ 4) (64 * inputHeight N) tree.word.length k
    (by omega) (by omega) (hddef.symm ▸ (computed_coarse_depth N n (by omega) hn hell).2)
    hbSize hqSize hLSize hnSize hkSize
  simpa only [initialThresholdQ, initialLambda, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    using hraw.trans hscalar

end EditApproximation

end OAI
