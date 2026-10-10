import OAI.Combinatorics.Progressions.Fourier.BohrLocalMomentAlternatives

namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_scale_for_local_convolution_alternatives
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular) (M : ℝ)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ kappa : ℝ≥0, 0 < kappa ∧
      ∀ (S : Finset (ZMod N)), S.Nonempty → S ⊆ (L.ndilate kappa).carrier →
      ∀ (f g : ZMod N → ℝ),
        (∀ x, x ∉ L.carrier → f x = 0) →
        (∀ x, x ∉ L.carrier → g x = 0) →
        (∑ x, f x) / (L.carrier.card : ℝ) = 1 →
        (∑ x, g x) / (L.carrier.card : ℝ) = 1 →
        (∀ x, 0 ≤ f x ∧ f x ≤ M) →
        (∀ x, 0 ≤ g x ∧ g x ≤ M) →
      ∀ (m : ℕ), 0 < m →
        sumLp S (fun x => convolution L.carrier f g x - 1) (2 * m) ≤ delta ∨
          ∃ h : ZMod N → ℝ, (h = f ∨ h = g) ∧ ∃ m' : ℕ,
            0 < m' ∧ m ≤ m' ∧ m' ≤ localMomentExponentFactor delta * m ∧
            1 + localMomentGain delta ≤ differenceLp S (correlation L.carrier h h) (2 * m') := by
  obtain ⟨kappa, hkappa0, hkappa, hsmall⟩ :=
    exists_localMomentScale L.rank (M := max M 1)
      (lt_of_lt_of_le (by norm_num) (le_max_right M 1)) hdelta
  refine ⟨kappa, hkappa0, ?_⟩
  intro S hS hSL f g hfsupport hgsupport hfnorm hgnorm hf hg m hm
  have hcard : (L.carrier.card : ℝ) ≠ 0 := by exact_mod_cast L.card_pos.ne'
  have hfsum : ∑ x, f x = (L.carrier.card : ℝ) := by
    simpa only [one_mul] using (div_eq_iff hcard).mp hfnorm
  have hgsum : ∑ x, g x = (L.carrier.card : ℝ) := by
    simpa only [one_mul] using (div_eq_iff hcard).mp hgnorm
  apply local_alternatives_of_regular_bohr L hL S hS hSL hkappa f g
    hfsupport hgsupport hfsum hgsum (M := max M 1) _ _ hdelta hsmall hm
  · intro x
    rw [abs_of_nonneg (hf x).1]
    exact (hf x).2.trans (le_max_left M 1)
  · intro x
    rw [abs_of_nonneg (hg x).1]
    exact (hg x).2.trans (le_max_left M 1)

end Erdos3.LocalConvolution

end

end OAI
