import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLargestRoles

namespace OAI

/-! Exact long-bin decomposition of a stopped coefficient. The
complementary short-bin part is supported on genuinely smooth integers. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedShortBinTest (B ρ y : ℝ) (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r d : Eisenstein) : Prop :=
  stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early r d ∧
    geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice (r*d))) < y/2

def stoppedLongBins (B ρ y : ℝ) : Finset ℕ :=
  (Finset.range (geometricBinCount ρ B)).filter (fun j => y/2 ≤ geometricBinLower ρ B j)

lemma stoppedBeta_product_predicate (R D : Finset Eisenstein) (f : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop)
    (P : Eisenstein → Prop) (n : Eisenstein) :
    stoppedBeta R D f ψ w (fun r d => selected r d ∧ P (r*d)) n =
      if P n then stoppedBeta R D f ψ w selected n else 0 := by
  unfold stoppedBeta primaryPairCoefficient
  by_cases hP : P n
  · rw [ite_eq_left hP]
    apply Finset.sum_congr rfl
    intro t ht
    have he := (Finset.mem_filter.mp ht).2
    simp only [he,hP,and_true]
  · rw [ite_eq_right hP]
    apply Finset.sum_eq_zero
    intro t ht
    have he := (Finset.mem_filter.mp ht).2
    simp only [he,hP,and_false,ite_false]

lemma largestPrimeChoice_valid_bin {B ρ : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) (hnorm : 1 < norm n)
    (hnB : norm n ≤ B) :
    primaryPrime (largestPrimeChoice n) ∧
      geometricPrimeBin ρ B (largestPrimeChoice n) < geometricBinCount ρ B := by
  have hne : (primaryPrimeFactors n).Nonempty := by
    by_contra hempty
    have he := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hp := primaryPrimeFactors_prod hn hs
    rw [he,Finset.prod_empty] at hp
    have hnormone : norm n = 1 := by rw [←hp,norm_one_eq]
    linarith
  have hp := primaryPrimeFactor_spec hn (largestPrimeChoice_spec hne).1
  exact ⟨hp.1,geometricPrimeBin_index hρ hρ₂ hp.1
    ((norm_le_of_dvd_nonzero (primary_ne_zero hn) hp.2).trans hnB)⟩

theorem stoppedBeta_long_bin_decomposition (R D : Finset Eisenstein) (f : Eisenstein → ℂ)
    (w B ρ y : ℝ) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (hnorm : 1 < norm n) (hnB : norm n ≤ B) :
    stoppedBeta R D f primeDetectorCutoff w
        (stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early) n =
      stoppedBeta R D f primeDetectorCutoff w (stoppedShortBinTest B ρ y j₀ k h Z Q early) n+
      ∑ j ∈ stoppedLongBins B ρ y,
        stoppedBeta R D f primeDetectorCutoff w (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n := by
  let s := stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early
  let c := geometricPrimeBin ρ B (largestPrimeChoice n)
  let z := stoppedBeta R D f primeDetectorCutoff w s n
  have hc : c < geometricBinCount ρ B := (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).2
  have heq (j : ℕ) :
      stoppedBeta R D f primeDetectorCutoff w (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n =
        if c = j then z else 0 := by
    have hpred : stoppedLargestBinTest B ρ j j₀ k h Z Q early =
        (fun r d => s r d ∧ geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j) := by
      funext r d
      rfl
    rw [hpred]
    have hb := stoppedBeta_product_predicate R D f primeDetectorCutoff w s
      (fun x => geometricPrimeBin ρ B (largestPrimeChoice x) = j) n
    by_cases hh : geometricPrimeBin ρ B (largestPrimeChoice n) = j
    · simpa only [stoppedLargestBinTest,s,c,z,hh,ite_true] using hb
    · simpa only [stoppedLargestBinTest,s,c,z,hh,ite_false] using hb
  have hshort : stoppedBeta R D f primeDetectorCutoff w (stoppedShortBinTest B ρ y j₀ k h Z Q early) n =
      if geometricBinLower ρ B c < y/2 then z else 0 :=
    stoppedBeta_product_predicate R D f primeDetectorCutoff w s
      (fun x => geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice x)) < y/2) n
  simp_rw [heq]
  rw [hshort]
  have hsum : (∑ j ∈ stoppedLongBins B ρ y, if c = j then z else 0) =
      if c ∈ stoppedLongBins B ρ y then z else 0 := by simp
  rw [hsum]
  have hmem : c ∈ stoppedLongBins B ρ y ↔ y/2 ≤ geometricBinLower ρ B c := by
    simp only [stoppedLongBins,Finset.mem_filter,Finset.mem_range,hc,true_and]
  rw [if_congr hmem rfl rfl]
  by_cases hsmall : geometricBinLower ρ B c < y/2
  · simp only [hsmall,not_le_of_gt hsmall,ite_true,ite_false,add_zero]
    rfl
  · simp only [hsmall,le_of_not_gt hsmall,ite_true,ite_false,zero_add]
    rfl

theorem stopped_short_bin_smooth {B ρ y : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) (hnorm : 1 < norm n)
    (hnB : norm n ≤ B)
    (hshort : geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice n)) < y/2) :
    ∀ p ∈ primaryPrimeFactors n, norm p ≤ y := by
  have hp := (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).1
  have hd := (largestPrimeChoice_prime_of_bin
    (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).2 hn rfl).2
  have hcell := (geometricPrimeBin_cell hρ hρ₂ hp
    ((norm_le_of_dvd_nonzero (primary_ne_zero hn) hd).trans hnB)).2
  have hlast : norm (largestPrimeChoice n) < y := by
    have hlower : 0 < geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice n)) := by
      exact zero_lt_one.trans (geometricBinLower_gt_one hρ
        (largestPrimeChoice_valid_bin hρ hρ₂ hn hs hnorm hnB).2)
    nlinarith
  intro p hp
  have hne : (primaryPrimeFactors n).Nonempty := ⟨p,hp⟩
  have hlarge := (largestPrimeChoice_spec hne).2 p hp
  have hnat : normNat p ≤ normNat (largestPrimeChoice n) := by
    rcases hlarge with hl | he
    · exact hl.le
    · exact he.1.le
  have hnormle : norm p ≤ norm (largestPrimeChoice n) := by
    rw [←normNat_cast,←normNat_cast]
    exact_mod_cast hnat
  exact hnormle.trans hlast.le

end CubicFirstMoment

end

end OAI
