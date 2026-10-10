import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralActionGronwall

namespace OAI

/-! The residual correction is small relative to the same action scale when
its scaled integral is small. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_action_convolution_bound
    (a r A : ℝ) (har : a≤ r) (hA : 0≤ A) (X g H : ℝ → ℝ)
    (hX : ContinuousOn X (Icc a r)) (hg : ContinuousOn g (Icc a r))
    (hH : ContinuousOn H (Icc a r)) (hg0 : ∀ t ∈ Icc a r, 0≤ g t)
    (hbound : ∀ t ∈ Icc a r, X t≤ A*Real.exp (H t+∫ s in a..t, g s)) :
    (∫ t in a..r, g t*Real.exp (H r-H t)*X t)≤
      A*Real.exp (H r+∫ s in a..r, g s)*(∫ t in a..r, g t) := by
  have hG (t : ℝ) (ht : t ∈ Icc a r) : (∫ s in a..t, g s)≤∫ s in a..r, g s := by
    have h1 : IntervalIntegrable g volume a t := ContinuousOn.intervalIntegrable_of_Icc ht.1
      (hg.mono (Icc_subset_Icc le_rfl ht.2))
    have h2 : IntervalIntegrable g volume t r := ContinuousOn.intervalIntegrable_of_Icc ht.2
      (hg.mono (Icc_subset_Icc ht.1 le_rfl))
    have ha := intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hn : 0≤∫ s in t..r, g s :=
      intervalIntegral.integral_nonneg ht.2 (fun s hs => hg0 s ⟨ht.1.trans hs.1,hs.2⟩)
    linarith
  have hleft : ContinuousOn (fun t => g t*Real.exp (H r-H t)*X t) (Icc a r) :=
    (hg.mul (Real.continuous_exp.comp_continuousOn (continuousOn_const.sub hH))).mul hX
  have hright : ContinuousOn (fun t => (A*Real.exp (H r+∫ s in a..r, g s))*g t) (Icc a r) :=
    continuousOn_const.mul hg
  calc
    _ ≤ ∫ t in a..r, (A*Real.exp (H r+∫ s in a..r, g s))*g t := by
      apply intervalIntegral.integral_mono_on har
        (ContinuousOn.intervalIntegrable_of_Icc har hleft)
        (ContinuousOn.intervalIntegrable_of_Icc har hright)
      intro t ht
      calc
        _ ≤ g t*Real.exp (H r-H t)*(A*Real.exp (H t+∫ s in a..t, g s)) :=
          mul_le_mul_of_nonneg_left (hbound t ht) (mul_nonneg (hg0 t ht) (Real.exp_pos _).le)
        _ = g t*A*Real.exp (H r+∫ s in a..t, g s) := by
          have he : Real.exp (H r-H t)*Real.exp (H t+∫ s in a..t, g s)=
              Real.exp (H r+∫ s in a..t, g s) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            _ = g t*A*(Real.exp (H r-H t)*Real.exp (H t+∫ s in a..t, g s)) := by ring
            _ = _ := by rw [he]
        _ ≤ g t*A*Real.exp (H r+∫ s in a..r, g s) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (add_le_add le_rfl (hG t ht)))
            (mul_nonneg (hg0 t ht) hA)
        _ = _ := by ring
    _ = _ := intervalIntegral.integral_const_mul _ _

end DefocusingNLS

end OAI
