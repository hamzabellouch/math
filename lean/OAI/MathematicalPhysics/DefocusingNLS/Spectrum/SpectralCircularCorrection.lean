import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularFieldBound

namespace OAI

/-! Weighted correction for the actual coupled circular coefficient field. -/

namespace DefocusingNLS

theorem exists_circular_correction (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (M κ : ℝ) (q : ℝ → ℂ) (hq : Continuous q) (hqM : ∀ t, ‖q t‖ ≤ M)
    (hκ : circularFieldBound νp νm η m M < κ) (r : CircularTailSpace) :
    ∃ v : CircularTailSpace,
      ‖v‖ ≤ ‖r‖/(κ-circularFieldBound νp νm η m M) ∧
      ∀ t, HasDerivAt (circularTailEvaluation v)
        (κ • circularTailEvaluation v t+circularLeadingField t (circularTailEvaluation v t)+
          circularBoundedField νp νm η m (q t) (circularTailEvaluation v t)+
          circularTailEvaluation r t) t := by
  let L := circularFieldBound νp νm η m M
  let N := fun t z => circularBoundedField νp νm η m (q t) z+circularTailEvaluation r t
  have hL : 0 ≤ L := circularFieldBound_nonneg νp νm η m M
  have hκ0 : 0 < κ := lt_of_le_of_lt hL hκ
  have hN : Continuous (Function.uncurry N) := by
    exact ((circularBoundedField_continuous νp νm η m).comp
      ((hq.comp continuous_fst).prodMk continuous_snd)).add
      ((circularTailEvaluation_continuous r).comp continuous_fst)
  have hN0 : ∀ t, ‖N t 0‖ ≤ ‖r‖ := by
    intro t
    dsimp [N]
    rw [circularBoundedField_zero,zero_add]
    exact circularTailEvaluation_norm r t
  have hLip : ∀ t z w, ‖N t z-N t w‖ ≤ L*‖z-w‖ := by
    intro t z w
    simpa only [N,add_sub_add_right_eq_sub] using
      circularBoundedField_difference νp νm η m hm M (q t) (hqM t) z w
  obtain ⟨v,hv,_,hd⟩ := exists_circular_weighted_ODE κ L ‖r‖ hκ0 hL hκ (norm_nonneg r)
    N hN hN0 hLip
  refine ⟨v,hv,?_⟩
  intro t
  simpa only [N,add_assoc] using hd t

end DefocusingNLS

end OAI
