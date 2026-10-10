import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughSupport

namespace OAI

/-! Exact transport between geometric bins with two ambient norm cutoffs.
Below the smaller cutoff the bin labels differ by one fixed integer, and
the corresponding lower endpoints and prefix sets agree. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma geometricBinCount_mono {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) :
    geometricBinCount ρ X ≤ geometricBinCount ρ F := by
  exact Nat.ceil_mono (div_le_div_of_nonneg_right
    (Real.log_le_log hX hXF) (Real.log_pos hρ).le)

lemma geometricPrimeBin_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) {p : Eisenstein}
    (hp : primaryPrime p) (hpX : norm p ≤ X) :
    geometricPrimeBin ρ F p = geometricPrimeBin ρ X p +
      (geometricBinCount ρ F-geometricBinCount ρ X) := by
  have hc := geometricBinCount_mono hρ hX hXF
  have hpn : 0 < norm p := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (primaryPrime_norm_ge_two hp)
  have hk : ⌊Real.log (norm p)/Real.log ρ⌋₊ ≤ geometricBinCount ρ X :=
    (Nat.floor_mono (div_le_div_of_nonneg_right (Real.log_le_log hpn hpX)
      (Real.log_pos hρ).le)).trans (Nat.floor_le_ceil _)
  unfold geometricPrimeBin
  omega

lemma geometricBinLower_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (j : ℕ) :
    geometricBinLower ρ F (j+(geometricBinCount ρ F-geometricBinCount ρ X)) =
      geometricBinLower ρ X j := by
  have hc := geometricBinCount_mono hρ hX hXF
  unfold geometricBinLower
  congr 1
  omega

lemma geometricPrimeBin_finset_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X) (j : ℕ) :
    primeBin s (geometricPrimeBin ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) =
      primeBin s (geometricPrimeBin ρ X) j := by
  ext p
  by_cases hp : p ∈ s
  · simp only [primeBin,Finset.mem_filter,hp,true_and,
      geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2,
      Nat.add_right_cancel_iff]
  · simp only [primeBin,Finset.mem_filter,hp,false_and]

lemma geometricPrimeBin_prefix_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X) (j : ℕ) :
    primeBinPrefix s (geometricPrimeBin ρ F)
        (j+(geometricBinCount ρ F-geometricBinCount ρ X)) =
      primeBinPrefix s (geometricPrimeBin ρ X) j := by
  ext p
  by_cases hp : p ∈ s
  · simp only [primeBinPrefix,Finset.mem_filter,hp,true_and,
      geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2,
      Nat.add_lt_add_iff_right]
  · simp only [primeBinPrefix,Finset.mem_filter,hp,false_and]

lemma geometricPrimeSurrogate_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X) :
    primeSurrogate s (geometricPrimeBin ρ F) (geometricBinLower ρ F) =
      primeSurrogate s (geometricPrimeBin ρ X) (geometricBinLower ρ X) := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2,
    geometricBinLower_shift hρ hX hXF]

lemma geometricStoppingPrimeSetTest_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) (s : Finset Eisenstein)
    (hs : ∀ p ∈ s, primaryPrime p ∧ norm p ≤ X)
    (j k : ℕ) (Z : ℝ) (r : Eisenstein) :
    stoppingPrimeSetTest s (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k Z r ↔
    stoppingPrimeSetTest s (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k Z r := by
  have hall : (∀ p ∈ s, geometricPrimeBin ρ F p ≤
      j+(geometricBinCount ρ F-geometricBinCount ρ X)) ↔
      ∀ p ∈ s, geometricPrimeBin ρ X p ≤ j := by
    constructor
    · intro h p hp
      have he := h p hp
      rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2] at he
      omega
    · intro h p hp
      rw [geometricPrimeBin_shift hρ hX hXF (hs p hp).1 (hs p hp).2]
      exact Nat.add_le_add_right (h p hp) _
  unfold stoppingPrimeSetTest
  rw [hall,geometricPrimeBin_finset_shift hρ hX hXF s hs,
    geometricPrimeSurrogate_shift hρ hX hXF s hs,geometricBinLower_shift hρ hX hXF]

lemma geometricStoppedSideTest_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) {d : Eisenstein}
    (hd : primary d) (hdX : norm d ≤ X)
    (j k h : ℕ) (Z Q : ℝ) (early : Bool) (r : Eisenstein) :
    stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
      (j+(geometricBinCount ρ F-geometricBinCount ρ X)) k
      (h+(geometricBinCount ρ F-geometricBinCount ρ X)) Z Q early r d ↔
    stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early r d := by
  have hs (p : Eisenstein) (hp : p ∈ primaryPrimeFactors d) :
      primaryPrime p ∧ norm p ≤ X :=
    ⟨(primaryPrimeFactor_spec hd hp).1,
      (norm_le_of_dvd (primary_ne_zero hd) (primaryPrimeFactor_spec hd hp).2).trans hdX⟩
  have hprefix := geometricPrimeBin_prefix_shift hρ hX hXF (primaryPrimeFactors d) hs h
  have hsur := geometricPrimeSurrogate_shift hρ hX hXF
    (primeBinPrefix (primaryPrimeFactors d) (geometricPrimeBin ρ X) h)
    (fun p hp => hs p (Finset.mem_filter.mp hp).1)
  unfold stoppedSideTest stoppingSideTest
  rw [geometricStoppingPrimeSetTest_shift hρ hX hXF (primaryPrimeFactors d) hs,
    hprefix,hsur]

end CubicFirstMoment

end

end OAI
