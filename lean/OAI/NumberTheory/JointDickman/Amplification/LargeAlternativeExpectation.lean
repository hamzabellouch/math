import OAI.NumberTheory.JointDickman.Amplification.LargeAlternativeCount

namespace OAI

/-! # Averaging the injective count before applying the numeric sieve -/

namespace JointDickman
open Finset Classical

noncomputable def tiltedLargeHighPairCount (B L k j d f : ℕ) (τ C Δ : ℝ)
    (A D V : Finset ℕ) : ℝ :=
  ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
      if RegularPrimeSet B L τ C U then
        ((largeHighAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) else 0

theorem tiltedLargeHighPairCount_le_classes {B L k j d f : ℕ} {τ C Δ : ℝ}
    (A D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : A ⊆ auxiliaryPrimes B)
    (hAr : RegularPrimeSet B L τ C A) (hDr : RegularPrimeSet B L τ C D)
    (hVr : RegularPrimeSet B L τ C V) :
    tiltedLargeHighPairCount B L k j d f τ C Δ A D V ≤
      ∑ Oa ∈ omissionEnvelope B L k τ A d,
        ∑ Od ∈ omissionEnvelope B L k τ D f,
          ∑ Y ∈ regularPrefixChoices B L k V f,
            tiltedRegularSubsetCount B L τ C A
              (activeHighAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
                ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d) := by
  let μ := fun U => bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U
  let E := omissionEnvelope B L k τ A d
  let F := omissionEnvelope B L k τ D f
  let P := regularPrefixChoices B L k V f
  let G := fun Oa Od Y => activeHighAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
    ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d
  have hmass (U : Finset ℕ) (hU : U ∈ (auxiliaryPrimes B \ A).powerset) : 0 ≤ μ U := by
    apply bernoulliSubsetMass_nonneg (mem_powerset.mp hU)
    intro p hp
    have hprime := auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    constructor
    · apply div_nonneg (by norm_num)
      linarith
    · apply (div_le_one (by linarith : (0 : ℝ) < 2*p-1)).mpr
      linarith
  have hpoint (U : Finset ℕ) (hU : U ∈ (auxiliaryPrimes B \ A).powerset) :
      μ U*(if RegularPrimeSet B L τ C U then
        ((largeHighAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) else 0) ≤
      ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P,
        μ U*(if RegularPrimeSet B L τ C U then (((G Oa Od Y).filter (fun Z => Z ⊆ U)).card : ℝ) else 0) := by
    by_cases hUr : RegularPrimeSet B L τ C U
    · simp only [hUr,ite_true]
      have hc : ((largeHighAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) ≤
          ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P, (((G Oa Od Y).filter (fun Z => Z ⊆ U)).card : ℝ) := by
        exact_mod_cast largeHighAlternativePairs_count A U D V hk hτ hℓ hA (mem_powerset.mp hU) hAr hUr hDr hVr
      simpa only [mul_sum] using mul_le_mul_of_nonneg_left hc (hmass U hU)
    · simp [hUr]
  calc
    _ ≤ ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P,
          μ U*(if RegularPrimeSet B L τ C U then (((G Oa Od Y).filter (fun Z => Z ⊆ U)).card : ℝ) else 0) :=
      sum_le_sum hpoint
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro Oa _
      rw [sum_comm]
      apply sum_congr rfl
      intro Od _
      rw [sum_comm]
      rfl

end JointDickman

end OAI
