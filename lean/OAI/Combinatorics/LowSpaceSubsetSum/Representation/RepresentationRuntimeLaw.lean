import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSamplingLoss
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationProgram

namespace OAI

/-! # Exact sign-coordinate transport to the input-only runtime experiment -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped symmDiff
attribute [local instance] Classical.propDecidable

namespace FiniteLaw

theorem map_equiv_mass {α β : Type} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (e : α ≃ β) (b : β) :
    (μ.map e).mass b = μ.mass (e.symm b) := by
  change μ.probability (fun a => e a = b) = _
  have he : (fun a => e a = b) = (fun a => a = e.symm b) := by
    funext a
    exact propext e.eq_symm_apply.symm
  rw [he, probability_eq]

theorem map_equiv_eq_of_mass {α β : Type} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (e : α ≃ β)
    (h : ∀ a, ν.mass (e a) = μ.mass a) : μ.map e = ν := by
  apply eq_of_mass
  intro b
  rw [map_equiv_mass]
  simpa only [e.apply_symm_apply] using (h (e.symm b)).symm

end FiniteLaw

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def runtimePrimeEquiv : R.PrimeHistory ≃ R.runtimeData.zeroSetup.PrimeHistory where
  toFun := R.runtimeHistory
  invFun h := ⟨⟨⟨(h.1.1.1.1, R.solution ∆ h.1.1.1.2), h.1.1.2⟩, h.1.2⟩, h.2⟩
  left_inv := by
    rintro ⟨⟨⟨⟨π, S⟩, g⟩, f⟩, p⟩
    exact congrArg (fun T : Finset (Fin n) =>
      (⟨⟨⟨(π, T), g⟩, f⟩, p⟩ : R.PrimeHistory)) (symmDiff_symmDiff_cancel_left R.solution S)
  right_inv := by
    rintro ⟨⟨⟨⟨π, S⟩, g⟩, f⟩, p⟩
    exact congrArg (fun T : Finset (Fin n) =>
      (⟨⟨⟨(π, T), g⟩, f⟩, p⟩ : R.runtimeData.zeroSetup.PrimeHistory))
        (symmDiff_symmDiff_cancel_left R.solution S)

def runtimeTrialEquiv : R.TrialHistory ≃ R.runtimeData.zeroSetup.TrialHistory where
  toFun h := ⟨R.runtimePrimeEquiv h.1, h.2⟩
  invFun h := ⟨R.runtimePrimeEquiv.symm h.1, h.2⟩
  left_inv := by
    rintro ⟨⟨⟨⟨⟨π, S⟩, g⟩, f⟩, p⟩, r⟩
    exact congrArg (fun T : Finset (Fin n) =>
      (⟨⟨⟨⟨(π, T), g⟩, f⟩, p⟩, r⟩ : R.TrialHistory))
        (symmDiff_symmDiff_cancel_left R.solution S)
  right_inv := by
    rintro ⟨⟨⟨⟨⟨π, S⟩, g⟩, f⟩, p⟩, r⟩
    exact congrArg (fun T : Finset (Fin n) =>
      (⟨⟨⟨⟨(π, T), g⟩, f⟩, p⟩, r⟩ : R.runtimeData.zeroSetup.TrialHistory))
        (symmDiff_symmDiff_cancel_left R.solution S)

def runtimeExtraEquiv : R.ExtraTrialHistory ≃ R.runtimeData.zeroSetup.ExtraTrialHistory where
  toFun h := ⟨R.runtimeTrialEquiv h.1, h.2⟩
  invFun h := ⟨R.runtimeTrialEquiv.symm h.1, h.2⟩
  left_inv := by
    rintro ⟨⟨⟨⟨⟨⟨π, S⟩, g⟩, f⟩, p⟩, r⟩, q⟩
    exact congrArg (fun T : Finset (Fin n) =>
      (⟨⟨⟨⟨⟨(π, T), g⟩, f⟩, p⟩, r⟩, q⟩ : R.ExtraTrialHistory))
        (symmDiff_symmDiff_cancel_left R.solution S)
  right_inv := by
    rintro ⟨⟨⟨⟨⟨⟨π, S⟩, g⟩, f⟩, p⟩, r⟩, q⟩
    exact congrArg (fun T : Finset (Fin n) =>
      (⟨⟨⟨⟨⟨(π, T), g⟩, f⟩, p⟩, r⟩, q⟩ : R.runtimeData.zeroSetup.ExtraTrialHistory))
        (symmDiff_symmDiff_cancel_left R.solution S)

def runtimeBucketEquiv (hn : 2200 ≤ n) :
    R.BucketTrialHistory hn ≃ R.runtimeData.zeroSetup.BucketTrialHistory hn where
  toFun h := ⟨R.runtimeExtraEquiv h.1, h.2⟩
  invFun h := ⟨R.runtimeExtraEquiv.symm h.1, h.2⟩
  left_inv := by
    rintro ⟨⟨⟨⟨⟨⟨⟨π, S⟩, g⟩, f⟩, p⟩, r⟩, q⟩, F⟩
    exact congrArg (fun T : Finset (Fin n) =>
      (⟨⟨⟨⟨⟨⟨(π, T), g⟩, f⟩, p⟩, r⟩, q⟩, F⟩ : R.BucketTrialHistory hn))
        (symmDiff_symmDiff_cancel_left R.solution S)
  right_inv := by
    rintro ⟨⟨⟨⟨⟨⟨⟨π, S⟩, g⟩, f⟩, p⟩, r⟩, q⟩, F⟩
    exact congrArg (fun T : Finset (Fin n) =>
      (⟨⟨⟨⟨⟨⟨(π, T), g⟩, f⟩, p⟩, r⟩, q⟩, F⟩ : R.runtimeData.zeroSetup.BucketTrialHistory hn))
        (symmDiff_symmDiff_cancel_left R.solution S)

/-- Every conditional sampler depends on the permutation and the guesses,
while this coordinate change alters only the independent sign subset. -/
theorem runtimePrime_mass (h : R.PrimeHistory) :
    R.runtimeData.zeroSetup.primeLaw.mass (R.runtimePrimeEquiv h) = R.primeLaw.mass h := by
  rfl

theorem runtimeTrial_mass (h : R.TrialHistory) :
    R.runtimeData.zeroSetup.trialLaw.mass (R.runtimeTrialEquiv h) = R.trialLaw.mass h := by
  rfl

theorem runtimeExtra_mass (hn : 100 ≤ n) (h : R.ExtraTrialHistory) :
    (R.runtimeData.zeroSetup.extraTrialLaw hn).mass (R.runtimeExtraEquiv h) =
      (R.extraTrialLaw hn).mass h := by
  rfl

theorem runtimeBucket_mass (hn : 10000 ≤ n) (h : R.BucketTrialHistory (by omega)) :
    (R.runtimeData.zeroSetup.bucketTrialLaw hn).mass (R.runtimeBucketEquiv (by omega) h) =
      (R.bucketTrialLaw hn).mass h := by
  rfl

theorem runtimePrime_law : R.primeLaw.map R.runtimePrimeEquiv = R.runtimeData.zeroSetup.primeLaw :=
  FiniteLaw.map_equiv_eq_of_mass _ _ _ R.runtimePrime_mass

theorem runtimeTrial_law : R.trialLaw.map R.runtimeTrialEquiv = R.runtimeData.zeroSetup.trialLaw :=
  FiniteLaw.map_equiv_eq_of_mass _ _ _ R.runtimeTrial_mass

theorem runtimeExtra_law (hn : 100 ≤ n) :
    (R.extraTrialLaw hn).map R.runtimeExtraEquiv = R.runtimeData.zeroSetup.extraTrialLaw hn :=
  FiniteLaw.map_equiv_eq_of_mass _ _ _ (R.runtimeExtra_mass hn)

theorem runtimeBucket_law (hn : 10000 ≤ n) :
    (R.bucketTrialLaw hn).map (R.runtimeBucketEquiv (by omega)) =
      R.runtimeData.zeroSetup.bucketTrialLaw hn :=
  FiniteLaw.map_equiv_eq_of_mass _ _ _ (R.runtimeBucket_mass hn)

theorem runtimeBucket_probability (hn : 10000 ≤ n)
    (P : R.runtimeData.zeroSetup.BucketTrialHistory (by omega) → Prop) :
    (R.runtimeData.zeroSetup.bucketTrialLaw hn).probability P =
      (R.bucketTrialLaw hn).probability (fun h => P (R.runtimeBucketEquiv (by omega) h)) := by
  rw [← R.runtimeBucket_law hn, FiniteLaw.map_probability]

/-- This is the actual input-only sampler, instantiated with the zero-target
wrapper. Its definition contains no chosen solution or analysis sign change. -/
def runtimeSampler (hn : 10000 ≤ n) :
    SamplerCoupling (R.runtimeData.zeroSetup.BucketTrialHistory (by omega)) :=
  R.runtimeData.zeroSetup.bucketHistoryCoupling hn

theorem runtimeSampler_failure (hn : 10000 ≤ n)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) :
    (R.runtimeSampler hn).failure ≤ (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 110 := by
  exact (R.runtimeData.zeroSetup.bucketHistoryCoupling_failure hn).trans
    (R.samplerError_guard hn hscale)

theorem runtimeSampler_event (hn : 10000 ≤ n)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (P : R.runtimeData.zeroSetup.BucketTrialHistory (by omega) → Prop) :
    (R.bucketTrialLaw hn).probability (fun h => P (R.runtimeBucketEquiv (by omega) h)) -
        (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 110 ≤
      (R.runtimeSampler hn).boundedLaw.probability (fun o => ∃ h, o = some h ∧ P h) := by
  have h := (R.runtimeSampler hn).event_lower P
  rw [runtimeSampler, R.runtimeData.zeroSetup.bucketHistoryCoupling_uniform,
    R.runtimeBucket_probability hn P] at h
  exact (sub_le_sub_left (R.runtimeSampler_failure hn hscale) _).trans h

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
