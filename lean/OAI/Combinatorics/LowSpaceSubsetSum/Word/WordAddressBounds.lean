import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSamplingBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedAsymptotics

namespace OAI

/-! # Finite random-word addresses fit the fixed machine word -/

noncomputable section
namespace LowSpaceSubsetSum.WordAddressBounds

def roundReads (n : ℕ) : ℕ := n*n^3+n^3+WordRealization.historyReads n

def totalReads {n : ℕ} (I : Instance n) : ℕ := inputScale I^120*roundReads n

theorem round_reads {n : ℕ} (I : Instance n) (hn : 10000 ≤ n) :
    roundReads n ≤ inputScale I^6*(compressionDictionaryCapacity n+1) := by
  let u := inputScale I
  let C := compressionDictionaryCapacity n
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hnu : n ≤ u := by unfold u inputScale; omega
  have hp : n*n^3+n^3 ≤ 2*u^4 := by
    have h1 : n*n^3 ≤ u^4 := by
      simpa only [←pow_succ'] using Nat.mul_le_mul hnu (Nat.pow_le_pow_left hnu 3)
    have h2 : n^3 ≤ u^4 := (Nat.pow_le_pow_left hnu 3).trans
      (Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 4))
    omega
  have hh := WordSamplingBounds.history_reads I hn
  change WordRealization.historyReads n ≤ u^5*(C+1) at hh
  have hs : 2*u^4 ≤ u^5*(C+1) := by
    have h1 : 2*u^4 ≤ u*u^4 := Nat.mul_le_mul_right _ (by omega)
    have h2 : u^5 ≤ u^5*(C+1) := Nat.le_mul_of_pos_right _ (by omega)
    rw [←pow_succ'] at h1
    exact h1.trans h2
  have hround : roundReads n ≤ 2*(u^5*(C+1)) := by
    unfold roundReads
    omega
  apply hround.trans
  calc
    _ ≤ u*(u^5*(C+1)) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [←Nat.mul_assoc,←pow_succ']

theorem total_reads {n : ℕ} (I : Instance n) (hn : 10000 ≤ n) :
    totalReads I ≤ inputScale I^126*(compressionDictionaryCapacity n+1) := by
  have h := Nat.mul_le_mul_left (inputScale I^120) (round_reads I hn)
  simpa only [totalReads,←Nat.mul_assoc,←pow_add] using h

theorem total_limit {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000) :
    totalReads I < 2^n := by
  have hu : (0 : ℝ) < inputScale I := by
    exact_mod_cast (show 0 < inputScale I by unfold inputScale; omega)
  have hC : (1 : ℝ) ≤ compressionDictionaryCapacity n := by
    exact_mod_cast (show 1 ≤ compressionDictionaryCapacity n from Nat.one_le_two_pow)
  have hc := PreparedAsymptotics.capacity_upper n
  have hsum : (compressionDictionaryCapacity n : ℝ)+1 ≤
      (2 : ℝ)^((199/1000 : ℝ)*n+1) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),Real.rpow_one]
    linarith only [hC,hc]
  have hs := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ (inputScale I : ℝ)^126 by positivity)
  have ht := guarded_polynomial_exponential hn hu hscale 126
    (a := (199/1000 : ℝ)) (by norm_num)
  have hb : ((totalReads I : ℕ) : ℝ) ≤
      (inputScale I : ℝ)^126*((compressionDictionaryCapacity n : ℝ)+1) := by
    exact_mod_cast total_reads I hn
  have hfin := hb.trans_lt (hs.trans_lt ht)
  exact_mod_cast hfin

theorem total_fits {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ)/1000000000) :
    totalReads I < 2^wordWidth I := cutoff_fits_word I (total_limit I hn hscale)

end LowSpaceSubsetSum.WordAddressBounds

end

end OAI
