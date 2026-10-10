import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorStoredSpace
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PrefixMachine

namespace OAI

/-! # Simultaneous representation workspace

The prefix control stack contains no collectors. During a right task the
left dictionary is retained; separator recursion uses filtered buffers only
after that task completes. The conservative bound below may even count the
task and checker workspaces simultaneously. Separator table storage is
shared throughout the trial.
-/

noncomputable section

namespace LowSpaceSubsetSum

namespace SeparatorCheck

variable {g : ℕ}

theorem family_depth_le (family : Array (Finset (Fin g)))
    (h : family.size ≤ 11 * 2 ^ g) :
    Nat.clog 2 family.size ≤ g + 4 := by
  apply Nat.clog_le_of_le_pow (b := 2)
  calc
    family.size ≤ 11 * 2 ^ g := h
    _ ≤ 2 ^ (g + 4) := by rw [pow_add]; norm_num; omega

theorem blocks_depth_sum_le (families : Fin 4 → Array (Finset (Fin g)))
    (h : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    ((blocks families).map (fun b => SeparatorBlocks.depth b + 1)).sum ≤ 4 * (g + 5) := by
  simp only [blocks, List.map_ofFn, List.sum_ofFn]
  change (∑ i : Fin 4, (Nat.clog 2 (families i).size + 1)) ≤ _
  calc
    _ ≤ (∑ _ : Fin 4, (g + 5)) := Finset.sum_le_sum (fun i _ => by
      change Nat.clog 2 (families i).size + 1 ≤ g + 5
      have hd := family_depth_le (families i) (h i)
      omega)
    _ = _ := by simp

/-- The live separator buffers are bounded on all family outcomes. -/
theorem run_peak_small (n C : ℕ) (families : Fin 4 → Array (Finset (Fin g)))
    (target : ℤ) (xs ys : List (Record g)) (hg : g ≤ n)
    (hsize : xs.length + ys.length ≤ 2 * (C + 1))
    (hC : 2 * (C + 1) ≤ 2 ^ n)
    (hfamily : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (run n families target xs ys).peak ≤ 100 * (n + 5) * (C + 1) := by
  have hp := peak_capacity n (2 * (C + 1)) families target xs ys hsize hC
  have hd := blocks_depth_sum_le families hfamily
  have hm := Nat.mul_le_mul_left (2 * (2 * (C + 1))) hd
  unfold SeparatorBlocks.capacityPeak at hp
  have hg' : g + 5 ≤ n + 5 := by omega
  have hmul := Nat.mul_le_mul_left (8 * (C + 1)) hg'
  nlinarith only [hp, hm, hmul]

end SeparatorCheck

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem doubled_capacity_fits (hn : 10000 ≤ n) :
    2 * (compressionDictionaryCapacity n + 1) ≤ 2 ^ n := by
  let C := compressionDictionaryCapacity n
  have hC : 1 ≤ C := Nat.one_le_two_pow
  have he : 199 * n / 1000 + 2 ≤ n := by omega
  calc
    2 * (C + 1) ≤ 4 * C := by omega
    _ = 2 ^ (199 * n / 1000 + 2) := by
      unfold C compressionDictionaryCapacity
      rw [pow_add]
      norm_num
      omega
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) he

/-- A cell count for every indexed bit of each live separator record,
including a conservative node/header multiplier. -/
def separatorWorkingCells (h : R.PrimeHistory) (hn : 2200 ≤ n)
    (draws : R.SeparatorDraws h hn) (target : ℤ)
    (xs ys : List (SeparatorCheck.Record (2 * blockHalf n 0))) : ℕ :=
  12 * (n + 1) * (SeparatorCheck.run n (SeparatorCheck.sampledFamilies draws) target xs ys).peak

theorem separatorWorkingCells_bound (h : R.PrimeHistory) (hn : 10000 ≤ n)
    (draws : R.SeparatorDraws h (by omega)) (target : ℤ)
    (xs ys : List (SeparatorCheck.Record (2 * blockHalf n 0)))
    (hsize : xs.length + ys.length ≤ 2 * (compressionDictionaryCapacity n + 1)) :
    R.separatorWorkingCells h (by omega) draws target xs ys ≤
      inputScale R.input ^ 4 * compressionDictionaryCapacity n := by
  let u := inputScale R.input
  let C := compressionDictionaryCapacity n
  let g := 2 * blockHalf n 0
  have hg : g ≤ n := by unfold g blockHalf; simp only [Matrix.cons_val_zero]; omega
  have hf : ∀ i, (SeparatorCheck.sampledFamilies draws i).size ≤ 11 * 2 ^ g := by
    intro i
    simpa only [SeparatorCheck.sampledFamilies, Array.size_ofFn,
      SeparatorExpectation.RoundedParameters.counts, SeparatorCheck.theta, g] using
      (separatorParameters h.1.1.2 (by omega)).counts_le i
  have hp := SeparatorCheck.run_peak_small n C (SeparatorCheck.sampledFamilies draws)
    target xs ys hg hsize (doubled_capacity_fits hn) hf
  have hnu : n + 1 ≤ u := by unfold u inputScale; omega
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hC : 1 ≤ C := Nat.one_le_two_pow
  have hnu5 : n + 5 ≤ 2 * u := by omega
  have hCp : C + 1 ≤ 2 * C := by omega
  have hpp : (SeparatorCheck.run n (SeparatorCheck.sampledFamilies draws) target xs ys).peak ≤
      400 * u * C := by
    apply hp.trans
    have hm := Nat.mul_le_mul hnu5 hCp
    nlinarith only [hm]
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 12 hnu) hpp
  have hpow : 4800 ≤ u ^ 2 := by nlinarith only [hu]
  have hfinal := Nat.mul_le_mul_right (u ^ 2 * C) hpow
  unfold separatorWorkingCells
  change 12 * (n + 1) * _ ≤ u ^ 4 * C
  nlinarith only [hprod, hfinal]

/-- All simultaneously allowed representation structures, with one retained
left dictionary, one task arena and the scalar prefix continuation stack. -/
def liveCells (task tables checker stack : ℕ) : ℕ :=
  task + tables + checker + stack +
    (n + 2) * (compressionDictionaryCapacity n + 1) + 16 * (n + 2) ^ 2

theorem liveCells_bound (hn : 10000 ≤ n) (task tables checker stack : ℕ)
    (htask : task ≤ inputScale R.input ^ 3 * compressionDictionaryCapacity n)
    (htables : tables ≤ inputScale R.input ^ 2 * compressionDictionaryCapacity n)
    (hchecker : checker ≤ inputScale R.input ^ 4 * compressionDictionaryCapacity n)
    (hstack : stack ≤ (4 * n + 16) * (n + 2)) :
    liveCells (n := n) task tables checker stack ≤
      inputScale R.input ^ 6 * compressionDictionaryCapacity n := by
  let u := inputScale R.input
  let C := compressionDictionaryCapacity n
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hn2 : n + 2 ≤ u := by unfold u inputScale; omega
  have hC : 1 ≤ C := Nat.one_le_two_pow
  have hs : stack ≤ 20 * u ^ 2 := by
    have ha : 4 * n + 16 ≤ 20 * u := by omega
    have hm := Nat.mul_le_mul ha hn2
    nlinarith only [hstack, hm]
  have hl : (n + 2) * (C + 1) ≤ 2 * u * C := by
    have hm := Nat.mul_le_mul hn2 (show C + 1 ≤ 2 * C by omega)
    nlinarith only [hm]
  have hb : 16 * (n + 2) ^ 2 ≤ 16 * u ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn2 2)
  have hu1 : 1 ≤ u := by omega
  have h2 : u ^ 2 ≤ u ^ 4 := Nat.pow_le_pow_right hu1 (by decide)
  have h3 : u ^ 3 ≤ u ^ 4 := Nat.pow_le_pow_right hu1 (by decide)
  have h1 : u ≤ u ^ 4 := le_self_pow hu1 (by decide)
  have hfree : 36 * u ^ 2 ≤ 36 * u ^ 4 * C := by
    have hh := Nat.mul_le_mul h2 hC
    nlinarith only [hh]
  have hsum : liveCells (n := n) task tables checker stack ≤ 41 * u ^ 4 * C := by
    unfold liveCells
    change task + tables + checker + stack + (n + 2) * (C + 1) + 16 * (n + 2) ^ 2 ≤ _
    have h2C := Nat.mul_le_mul_right C h2
    have h3C := Nat.mul_le_mul_right C h3
    have h1C := Nat.mul_le_mul_right C h1
    change task ≤ u ^ 3 * C at htask
    change tables ≤ u ^ 2 * C at htables
    change checker ≤ u ^ 4 * C at hchecker
    nlinarith only [htask, htables, hchecker, hs, hl, hb, h2C, h3C, h1C, hfree]
  apply hsum.trans
  have hp : 41 ≤ u ^ 2 := by nlinarith only [hu]
  have hh := Nat.mul_le_mul_right (u ^ 4 * C) hp
  nlinarith only [hh]

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
