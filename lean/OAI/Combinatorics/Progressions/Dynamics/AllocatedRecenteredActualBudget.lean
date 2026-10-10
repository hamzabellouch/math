import OAI.Combinatorics.Progressions.Estimates.AllocatedCoverLogBounds
import OAI.Combinatorics.Progressions.Sampling.AllocatedReferenceIdealSampling
import OAI.Combinatorics.Progressions.Sampling.AllocatedUnifiedSamplingBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedRecenteredActualSamplingBudget (m dim A : ℕ)
    (D P Pc e g pB E : ℝ) : ℝ :=
  let input := allocatedActualProfileInput m D Pc e g P
  max (allocatedUnifiedSamplingBudget m dim A P pB E)
    (allocatedProfileAccuracyBudget (allocatedProfileFourierInput input)
      (allocatedProfileFourierOutput input) (allocatedCoefficientAccuracyLog m pB (E + 3)))

theorem exists_allocatedRecenteredActualThreshold_bound (m dim A K : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {D P Pc e g pB E : ℝ},
      0 ≤ D → 0 ≤ P → 0 ≤ Pc → 0 ≤ e → 0 ≤ g → 0 ≤ pB → 0 ≤ E →
      (allocatedRecenteredActualSamplingBudget m dim A D P Pc e g pB E + K) ^ K ≤
        (D + P + Pc + e + g + pB + E + a) ^ a := by
  obtain ⟨c, _hc, hacc⟩ := exists_allocatedCoefficientAccuracyLog_bound m
  obtain ⟨b, _hb, hunified⟩ := exists_allocatedUnifiedSamplingThreshold_bound m dim A 1
  obtain ⟨d, _hd, hprofile⟩ := exists_allocatedActualProfileFourier_bound m
  let vp : Polynomial ℕ := (Polynomial.X + Polynomial.C d) ^ d
  let major : Polynomial ℕ := allocatedProfileAccuracyBudget vp vp
    ((Polynomial.X + 3 + Polynomial.C c) ^ c)
  let poly : Polynomial ℕ := ((Polynomial.X + Polynomial.C b) ^ b + major + Polynomial.C K) ^ K
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro D P Pc e g pB E hD hP hPc he hg hpB hE
  let s := D + P + Pc + e + g + pB + E
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hPpEs : P + pB + E ≤ s := by dsimp [s]; linarith only [hD, hPc, he, hg]
  have hpEs : pB + E ≤ s := by dsimp [s]; linarith only [hD, hP, hPc, he, hg]
  have hInputs : D + Pc + e + g + P ≤ s := by dsimp [s]; linarith only [hpB, hE]
  have hE3 : 0 ≤ E + 3 := by linarith only [hE]
  have haccBound : allocatedCoefficientAccuracyLog m pB (E + 3) ≤ (s + 3 + c) ^ c := by
    apply (hacc hpB hE3).trans
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hpEs]
  let u := allocatedActualProfileInput m D Pc e g P
  let v := (s + d) ^ d
  have hu : 0 ≤ u := (allocatedActualProfileInput_bounds m hD hPc he hg hP).1
  have hL0 : 0 ≤ allocatedProfileFourierInput u := by
    have h := allocatedProfileErrorLog_nonneg hu
    unfold allocatedProfileFourierInput
    positivity
  have hLP : allocatedProfileFourierInput u ≤ allocatedProfileFourierOutput u := by
    have hterm : 0 ≤ 2 * allocatedProfileFourierInput u * (2 * allocatedProfileFourierInput u + 2) ^ 4 := by positivity
    have hpow : 0 ≤ (2 * allocatedProfileFourierInput u + 2) ^ 4 := by positivity
    dsimp only [allocatedProfileFourierOutput]
    linarith only [hu, hterm, hpow]
  have hPout : allocatedProfileFourierOutput u ≤ v :=
    (hprofile hD hPc he hg hP).trans
      (pow_le_pow_left₀ (by positivity) (add_le_add hInputs (le_refl (d : ℝ))) d)
  have hL : allocatedProfileFourierInput u ≤ v := hLP.trans hPout
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hlog : 0 ≤ allocatedCoefficientAccuracyLog m pB (E + 3) :=
    neg_nonpos.mp (Real.exp_le_one_iff.mp (allocatedCoefficientAccuracy_bounds m hpB hE3).2.1)
  let q := allocatedProfileAccuracyBudget v v ((s + 3 + c) ^ c)
  have hq : 0 ≤ q := by dsimp only [q, allocatedProfileAccuracyBudget]; positivity
  have hactual : allocatedProfileAccuracyBudget (allocatedProfileFourierInput u)
      (allocatedProfileFourierOutput u) (allocatedCoefficientAccuracyLog m pB (E + 3)) ≤ q := by
    dsimp only [q, allocatedProfileAccuracyBudget]
    gcongr
  have hUni0 := (allocatedUnifiedSamplingBudget_bounds m dim A hP hpB hE).2.2.2.1
  have hUni : allocatedUnifiedSamplingBudget m dim A P pB E ≤ (s + b) ^ b := by
    have h := hunified hP hpB hE
    simp only [Nat.cast_one, pow_one] at h
    have h' : allocatedUnifiedSamplingBudget m dim A P pB E ≤ (P + pB + E + b) ^ b := by
      linarith only [h]
    exact h'.trans (pow_le_pow_left₀ (by positivity) (add_le_add hPpEs (le_refl (b : ℝ))) b)
  have hbudget : allocatedRecenteredActualSamplingBudget m dim A D P Pc e g pB E ≤ (s + b) ^ b + q := by
    apply max_le
    · exact hUni.trans (le_add_of_nonneg_right hq)
    · exact hactual.trans (le_add_of_nonneg_left (by positivity))
  have hbudget0 : 0 ≤ allocatedRecenteredActualSamplingBudget m dim A D P Pc e g pB E :=
    hUni0.trans (le_max_left _ _)
  calc
    _ ≤ ((s + b) ^ b + q + K) ^ K := pow_le_pow_left₀ (by positivity) (add_le_add hbudget (le_refl (K : ℝ))) K
    _ ≤ _ := by
      simpa [poly, major, vp, q, v, s, allocatedProfileAccuracyBudget,
        Polynomial.eval₂_pow] using hbound s hs

end Erdos3.VectorPolynomial

end

end OAI
