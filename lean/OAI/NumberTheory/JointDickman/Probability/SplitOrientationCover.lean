import OAI.NumberTheory.JointDickman.Probability.SplitChangeEvents
import OAI.NumberTheory.JointDickman.Probability.SplitProbabilityBounds

namespace OAI

/-! # Orienting the two-split event in its original symmetric law -/

namespace JointDickman

open Finset

def splitOrientationEvent {P : Finset ℕ} (E : TwoSiteSplit P → Prop)
    (Y : ℝ) (site : Bool) (x : TwoSiteSplit P) : Prop :=
  E x ∧ twoSiteNoHighChange x Y ∧ twoSiteAddition x Y site

/-- Orientation is performed before conditioning on the first coefficients.
Exchangeability accounts for the reverse direction with a factor of two. -/
theorem split_orientation_cover {B N : ℕ} (hB : 1 < B)
    (hcap : 4 * (B : ℝ) ≤ (2 : ℝ)^N * Real.log (auxiliaryCutoff B))
    (E : TwoSiteSplit (auxiliaryPrimes B) → Prop) (hE : ∀ x, E x.swap ↔ E x) :
    twoSiteSplitProbability (auxiliaryPrimes B) E ≤
      twoSiteSplitProbability (auxiliaryPrimes B) (fun x => E x ∧ twoSiteNoChange x) +
        2 * ∑ i ∈ Icc 1 N,
          (twoSiteSplitProbability (auxiliaryPrimes B) (splitOrientationEvent E (primeTailEndpoint B i) false) +
           twoSiteSplitProbability (auxiliaryPrimes B) (splitOrientationEvent E (primeTailEndpoint B i) true)) := by
  classical
  let G (i : ℕ) (b : Bool) := splitOrientationEvent E (primeTailEndpoint B i) b
  let F (i : ℕ) (x : TwoSiteSplit (auxiliaryPrimes B)) :=
    G i false x ∨ G i true x ∨ G i false x.swap ∨ G i true x.swap
  have hc : ∀ x, E x → (E x ∧ twoSiteNoChange x) ∨ ∃ i ∈ Icc 1 N, F i x := by
    intro x hx
    by_cases hn : twoSiteNoChange x
    · exact Or.inl ⟨hx, hn⟩
    · obtain ⟨i, hi, hh, ho⟩ := largest_changed_prime_shell hB hcap x hn
      refine Or.inr ⟨i, hi, ?_⟩
      have hxs := (hE x).mpr hx
      have hhs := (twoSiteNoHighChange_swap x (primeTailEndpoint B i)).mpr hh
      rcases ho with h | h | h | h
      · exact Or.inl ⟨hx, hh, h⟩
      · exact Or.inr (Or.inl ⟨hx, hh, h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hxs, hhs, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hxs, hhs, h⟩))
  have hcover := twoSiteSplitProbability_cover (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (Icc 1 N) E (fun x => E x ∧ twoSiteNoChange x) F hc
  have hf (i : ℕ) : twoSiteSplitProbability (auxiliaryPrimes B) (F i) ≤
      2 * (twoSiteSplitProbability (auxiliaryPrimes B) (G i false) +
        twoSiteSplitProbability (auxiliaryPrimes B) (G i true)) := by
    have hh := twoSiteSplitProbability_four_or (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
      (G i false) (G i true) (fun x => G i false x.swap) (fun x => G i true x.swap)
    rw [twoSiteSplitProbability_swap, twoSiteSplitProbability_swap] at hh
    change twoSiteSplitProbability (auxiliaryPrimes B) (F i) ≤ _ at hh
    convert hh using 1
    ring

  have hsum := sum_le_sum (fun i (_ : i ∈ Icc 1 N) => hf i)
  rw [← mul_sum] at hsum
  exact hcover.trans (add_le_add le_rfl hsum)

/-- The orientation bound for the actual simultaneous regular amplification events. -/
theorem amplification_orientation_cover {B N : ℕ} (L T : ℕ) (τ C : ℝ) (hB : 1 < B)
    (hcap : 4 * (B : ℝ) ≤ (2 : ℝ)^N * Real.log (auxiliaryCutoff B)) :
    twoSiteSplitProbability (auxiliaryPrimes B) (bothAmplificationSplitsGood B L T τ C) ≤
      twoSiteSplitProbability (auxiliaryPrimes B)
        (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) +
      2 * ∑ i ∈ Icc 1 N,
        (twoSiteSplitProbability (auxiliaryPrimes B)
          (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false) +
         twoSiteSplitProbability (auxiliaryPrimes B)
          (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true)) :=
  split_orientation_cover hB hcap _ (bothAmplificationSplitsGood_swap B L T τ C)

end JointDickman

end OAI
