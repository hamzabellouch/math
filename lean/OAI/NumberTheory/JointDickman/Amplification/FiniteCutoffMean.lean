import OAI.NumberTheory.JointDickman.Amplification.FiniteCutoffProfiles
import OAI.NumberTheory.JointDickman.Amplification.ArithmeticLongFluctuation

namespace OAI

/-! # The finite graph cutoffs preserve the vanishing arithmetic error -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem residueCandidateCutError_mean {B L T H M : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ) :
    (∑ r : ZMod (auxiliarySquarePeriod B), residueCandidateCutError B L T H M τ C χ r)/
        (auxiliarySquarePeriod B : ℝ) =
      arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ) := by
  have ht := real_periodic_moment_tendsto (residueCandidateCutError B L T H M τ C χ) 1
  simp only [pow_one,residueCandidateCutError_natCast hT χ] at ht
  exact tendsto_nhds_unique ht (actualCandidateCutError_mean_tendsto hT χ)

theorem finite_cutoff_sum_bound {B L T H M : ℕ} {τ C A E : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (hA : 0 ≤ A)
    (hcap : ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ u, |actualCandidateCutError B L T H M τ C χ u| ≤ A)
    (hmean : ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ) ≤ E)
    (N K : ℕ) :
    (∑ u ∈ range K, actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u) ≤
      (K : ℝ)*E+(Fintype.card (primeCandidatePool B M → Bool) : ℝ)*
        (2*(auxiliarySquarePeriod B : ℝ)*A) := by
  let F := fun (s : primeCandidatePool B M → Bool) =>
    residueCandidateCutError B L T H M τ C (profileCandidateCutoff B T M s)
  have hf (s : primeCandidatePool B M → Bool) (r : ZMod (auxiliarySquarePeriod B)) :
      |F s r| ≤ A := hcap _ (profileCandidateCutoff_bounds B T M s) r.val
  have hm (s : primeCandidatePool B M → Bool) :
      (∑ r, F s r)/(auxiliarySquarePeriod B : ℝ) ≤ E := by
    rw [show (∑ r, F s r)/(auxiliarySquarePeriod B : ℝ) =
      arithmeticSquareMean B (actualCandidateCutError B L T H M τ C
        (profileCandidateCutoff B T M s)) from residueCandidateCutError_mean hT _]
    exact hmean _ (profileCandidateCutoff_bounds B T M s)
  have hh := periodic_interval_profile_bound F hA hf hm (finiteCutProfile B M N)
    (finiteCutProfile_intervals B M N) K
  have heq u : F (finiteCutProfile B M N u) (u : ZMod (auxiliarySquarePeriod B)) =
      actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u := by
    dsimp only [F]
    rw [residueCandidateCutError_natCast hT,actualCandidateCutError_finiteProfile]
  simpa only [heq] using hh

theorem finite_cutoff_arithmetic_decay
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
        0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ N : ℕ,
          (∑ u ∈ range K, actualCandidateCutError B L T H M τ C
            (finiteCandidateCutoff B T N u) u)/(K : ℝ) < E B+ε := by
  obtain ⟨E,hE,hm⟩ := actual_arithmetic_fluctuation_decay hFord hMertens hL hτ hτsmall
  refine ⟨E,hE,?_⟩
  filter_upwards [hm,candidate_root_error_cap hL hτ hτsmall] with B hm hcap
  intro C T H M hT hTs hTP hM0 hM hMexp ε hε
  let A : ℝ := (Fintype.card (primeCandidatePool B M → Bool) : ℝ)*
    (2*(auxiliarySquarePeriod B : ℝ)*(B : ℝ)^10)
  have hlim : Tendsto (fun K : ℕ => A/(K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat A
  filter_upwards [hlim.eventually (Iio_mem_nhds hε),eventually_gt_atTop 0] with K hK hK0
  intro N
  have hs := finite_cutoff_sum_bound (L := L) (H := H) (τ := τ) (C := C) hTP
    (pow_nonneg (Nat.cast_nonneg B) 10)
    (fun χ hχ u => hcap C T H M hM0 hM (fun i => coefficientPrimeSet B (u+(i.val+1)))
      χ hχ (primeSiteTranspose _ (auxiliaryPrimes B)
        (arithmeticCandidatePrimeFamily B _ (candidateArithmeticQuotient u))))
    (fun χ hχ => hm C T H M hT hTs hTP hM0 hM hMexp χ hχ) N K
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  calc
    _ ≤ ((K : ℝ)*E B+A)/(K : ℝ) := div_le_div_of_nonneg_right hs hKr.le
    _ = E B+A/(K : ℝ) := by field_simp
    _ < E B+ε := by linarith only [hK]

end JointDickman

end OAI
