import OAI.Probability.SLE.Multipoint.MultipointInteractionShells

namespace OAI

/-! The source time normalization of the pair-interaction drop. The two
uncentered Loewner paths have velocity `a/(f-U)`, while the common real
driver is only assumed continuous. No derivative of Brownian motion is
used. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge.Multipoint

def loewnerPoissonRate (f : ℝ → ℂ) (U : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t).im / ‖f t - (U t : ℂ)‖ ^ 2

lemma loewnerPoissonRate_continuousOn
    {s T : ℝ} {f : ℝ → ℂ} {U : ℝ → ℝ}
    (hf : ContinuousOn f (Icc s T)) (hU : ContinuousOn U (Icc s T))
    (hfi : ∀ t ∈ Icc s T, 0 < (f t).im) :
    ContinuousOn (loewnerPoissonRate f U) (Icc s T) := by
  apply (Complex.continuous_im.comp_continuousOn hf).div
    ((hf.sub (Complex.continuous_ofReal.comp_continuousOn hU)).norm.pow 2)
  intro t ht
  apply pow_ne_zero 2
  apply norm_ne_zero_iff.mpr
  intro he
  have hi := congrArg Complex.im (sub_eq_zero.mp he)
  have hp := hfi t ht
  change (f t).im = 0 at hi
  linarith

lemma loewnerPoissonRate_nonneg
    {f : ℝ → ℂ} {U : ℝ → ℝ} {t : ℝ} (hfi : 0 ≤ (f t).im) :
    0 ≤ loewnerPoissonRate f U t := div_nonneg hfi (sq_nonneg _)

/-- Exact fundamental-theorem-of-calculus form of the interaction identity
in the manuscript's time normalization. -/
theorem loewner_interaction_drop
    {s T a : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T)
    (f g : ℝ → ℂ) (U : ℝ → ℝ) (hU : ContinuousOn U (Icc s T))
    (hf : ∀ t ∈ Icc s T, HasDerivWithinAt f ((a : ℂ) / (f t - (U t : ℂ))) (Ici 0) t)
    (hg : ∀ t ∈ Icc s T, HasDerivWithinAt g ((a : ℂ) / (g t - (U t : ℂ))) (Ici 0) t)
    (hfi : ∀ t ∈ Icc s T, 0 < (f t).im)
    (hgi : ∀ t ∈ Icc s T, 0 < (g t).im)
    (hne : ∀ t ∈ Icc s T, f t ≠ g t) :
    2 * a * (∫ t in s..T, loewnerPoissonRate f U t * loewnerPoissonRate g U t) =
      interaction (f s) (g s) - interaction (f T) (g T) := by
  let K := fun t => interaction (f t) (g t)
  let R := fun t => loewnerPoissonRate f U t * loewnerPoissonRate g U t
  have hfc : ContinuousOn f (Icc s T) := fun t ht =>
    ((hf t ht).mono (fun x hx => hs.trans hx.1)).continuousWithinAt
  have hgc : ContinuousOn g (Icc s T) := fun t ht =>
    ((hg t ht).mono (fun x hx => hs.trans hx.1)).continuousWithinAt
  have hRc : ContinuousOn R (Icc s T) :=
    (loewnerPoissonRate_continuousOn hfc hU hfi).mul
      (loewnerPoissonRate_continuousOn hgc hU hgi)
  have hd : ∀ t ∈ Icc s T, HasDerivWithinAt K ((-2 * a) * R t) (Ici 0) t := by
    intro t ht
    simpa only [K, R, loewnerPoissonRate, interaction_center, mul_assoc] using
      centered_interaction_hasDerivWithinAt U (hf t ht) (hg t ht)
        (hfi t ht) (hgi t ht) (hne t ht)
  have hKc : ContinuousOn K (Icc s T) := fun t ht =>
    ((hd t ht).mono (fun x hx => hs.trans hx.1)).continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hsT hKc
    (fun t ht => (hd t ⟨ht.1.le, ht.2.le⟩).mono
      (fun x hx => hs.trans (ht.1.le.trans hx.le)))
    ((continuousOn_const.mul hRc).intervalIntegrable_of_Icc hsT)
  rw [intervalIntegral.integral_const_mul] at he
  change (-2 * a) * (∫ t in s..T, R t) = K T - K s at he
  change 2 * a * (∫ t in s..T, R t) = K s - K T
  linarith

theorem loewner_interaction_future_bound
    {s T a : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (ha : 0 < a)
    (f g : ℝ → ℂ) (U : ℝ → ℝ) (hU : ContinuousOn U (Icc s T))
    (hf : ∀ t ∈ Icc s T, HasDerivWithinAt f ((a : ℂ) / (f t - (U t : ℂ))) (Ici 0) t)
    (hg : ∀ t ∈ Icc s T, HasDerivWithinAt g ((a : ℂ) / (g t - (U t : ℂ))) (Ici 0) t)
    (hfi : ∀ t ∈ Icc s T, 0 < (f t).im)
    (hgi : ∀ t ∈ Icc s T, 0 < (g t).im)
    (hne : ∀ t ∈ Icc s T, f t ≠ g t) :
    (∫ t in s..T, loewnerPoissonRate f U t * loewnerPoissonRate g U t) ≤
      interaction (f s) (g s) / (2 * a) := by
  have hd := loewner_interaction_drop hs hsT f g U hU hf hg hfi hgi hne
  have hp := interaction_nonneg (hfi T ⟨hsT, le_rfl⟩) (hgi T ⟨hsT, le_rfl⟩)
  apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
  nlinarith

/-- Source-normalized weighted interaction, with the interval drop
discharged from the actual Loewner ODE. Only the geometric decay remains
as a separate premise. -/
theorem loewner_weighted_interaction_integral_le
    {s T a c M : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (ha : 0 < a)
    (hM : 0 ≤ M) (hc : 0 ≤ c) (hca : 2 * c < a)
    (f g : ℝ → ℂ) (U : ℝ → ℝ) (hU : ContinuousOn U (Icc s T))
    (hf : ∀ t ∈ Icc s T, HasDerivWithinAt f ((a : ℂ) / (f t - (U t : ℂ))) (Ici 0) t)
    (hg : ∀ t ∈ Icc s T, HasDerivWithinAt g ((a : ℂ) / (g t - (U t : ℂ))) (Ici 0) t)
    (hfi : ∀ t ∈ Icc s T, 0 < (f t).im)
    (hgi : ∀ t ∈ Icc s T, 0 < (g t).im)
    (hne : ∀ t ∈ Icc s T, f t ≠ g t)
    (u v : ℝ → ℝ) (hu : ContinuousOn u (Icc s T)) (hv : ContinuousOn v (Icc s T))
    (hu0 : ∀ t ∈ Icc s T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc s T, 0 ≤ v t)
    (hdecay : ∀ t ∈ Icc s T, interaction (f t) (g t) ≤
      M * Real.exp (-a * max (u t) (v t))) :
    (∫ t in s..T, Real.exp (c * (u t + v t)) *
      (loewnerPoissonRate f U t * loewnerPoissonRate g U t)) ≤
        M * interactionBudget a c := by
  have hfc : ContinuousOn f (Icc s T) := fun t ht =>
    ((hf t ht).mono (fun x hx => hs.trans hx.1)).continuousWithinAt
  have hgc : ContinuousOn g (Icc s T) := fun t ht =>
    ((hg t ht).mono (fun x hx => hs.trans hx.1)).continuousWithinAt
  apply weighted_interaction_integral_le hsT ha hM hc hca u v
    (fun t => loewnerPoissonRate f U t * loewnerPoissonRate g U t)
    (fun t => interaction (f t) (g t)) hu hv hu0 hv0
    ((loewnerPoissonRate_continuousOn hfc hU hfi).mul
      (loewnerPoissonRate_continuousOn hgc hU hgi))
    (fun t ht => mul_nonneg (loewnerPoissonRate_nonneg (hfi t ht).le)
      (loewnerPoissonRate_nonneg (hgi t ht).le)) ?_ hdecay
  intro t ht
  have hsub : Icc t T ⊆ Icc s T := Icc_subset_Icc ht.1 le_rfl
  exact loewner_interaction_future_bound (hs.trans ht.1) ht.2 ha f g U (hU.mono hsub)
    (fun x hx => hf x (hsub hx)) (fun x hx => hg x (hsub hx))
    (fun x hx => hfi x (hsub hx)) (fun x hx => hgi x (hsub hx))
    (fun x hx => hne x (hsub hx))

end SLEExactGauge.Multipoint

end

end OAI
