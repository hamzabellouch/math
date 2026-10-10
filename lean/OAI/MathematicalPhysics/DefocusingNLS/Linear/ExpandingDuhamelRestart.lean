import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelContinuity

namespace OAI

/-! # Restarting the inhomogeneous moving-scale evolution

Splitting the Duhamel integral gives the exact restart identity at the
larger radius `L exp(s/2)`.  This permits uniform short slabs to be joined.
-/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingDuhamel_eq_intervalIntegral (a b k L t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t) (r : ℝ → FourierL2) :
    expandingDuhamel a b k L ha hk hL t r =
      ∫ τ in 0..t, expandingDuhamelIntegrand a b k L ha hk hL t r τ := by
  rw [expandingDuhamel, intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]

private theorem expandingFreeStep_after_kernel (a b k L s t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (r : ℝ → FourierL2) (τ : ℝ) (hτ : τ ∈ Icc 0 s) :
    expandingFreeStep a b k (expandingRadius L s) t ha hk
      (hL.trans (expandingRadius_ge L s hL hs)) ht
      (expandingDuhamelIntegrand a b k L ha hk hL s r τ) =
        expandingDuhamelIntegrand a b k L ha hk hL (s + t) r τ := by
  change 0 ≤ τ ∧ τ ≤ s at hτ
  have hτ' : τ ∈ Icc 0 (s + t) := ⟨hτ.1, by linarith [hτ.2]⟩
  rw [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ,
    expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ']
  have hR : expandingRadius (expandingRadius L τ) (s - τ) = expandingRadius L s := by
    rw [expandingRadius_add]
    congr 1
    ring
  have hd : (s - τ) + t = (s + t) - τ := by ring
  have h := congrArg (fun A : FourierL2 →L[ℂ] FourierL2 => A (r τ))
    (expandingFreeStep_add a b k (expandingRadius L τ) (s - τ) t ha hk
      (hL.trans (expandingRadius_ge L τ hL hτ.1)) (sub_nonneg.mpr hτ.2) ht)
  simp only [ContinuousLinearMap.comp_apply] at h
  simpa only [hR, hd] using h

private theorem expanding_shifted_kernel (a b k L s t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (r : ℝ → FourierL2) (τ : ℝ) (hτ : τ ∈ Icc 0 t) :
    expandingDuhamelIntegrand a b k L ha hk hL (s + t) r (s + τ) =
      expandingDuhamelIntegrand a b k (expandingRadius L s) ha hk
        (hL.trans (expandingRadius_ge L s hL hs)) t (fun u => r (s + u)) τ := by
  change 0 ≤ τ ∧ τ ≤ t at hτ
  have hτ' : s + τ ∈ Icc 0 (s + t) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  rw [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ',
    expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ]
  congr 2
  · exact (expandingRadius_add L s τ).symm
  · ring

/-- Exact inhomogeneous restart, with the radius advanced at the restart time. -/
theorem expandingDuhamel_restart (a b k L s t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 (s + t))) :
    expandingDuhamel a b k L ha hk hL (s + t) r =
      expandingFreeStep a b k (expandingRadius L s) t ha hk
        (hL.trans (expandingRadius_ge L s hL hs)) ht
        (expandingDuhamel a b k L ha hk hL s r) +
      expandingDuhamel a b k (expandingRadius L s) ha hk
        (hL.trans (expandingRadius_ge L s hL hs)) t (fun u => r (s + u)) := by
  let F := expandingDuhamelIntegrand a b k L ha hk hL (s + t) r
  have hs' : s ≤ s + t := by linarith
  have hr₀ : ContinuousOn r (Icc 0 s) := hr.mono (Icc_subset_Icc le_rfl hs')
  have hc : ContinuousOn F (Icc 0 (s + t)) :=
    continuousOn_expandingDuhamelIntegrand a b k L ha hk hL (s + t) r hr
  have h₁ : IntervalIntegrable F volume 0 s :=
    (hc.mono (Icc_subset_Icc le_rfl hs')).intervalIntegrable_of_Icc hs
  have h₂ : IntervalIntegrable F volume s (s + t) :=
    (hc.mono (Icc_subset_Icc hs le_rfl)).intervalIntegrable_of_Icc hs'
  have hfirst : (∫ τ in 0..s, F τ) =
      expandingFreeStep a b k (expandingRadius L s) t ha hk
        (hL.trans (expandingRadius_ge L s hL hs)) ht
        (expandingDuhamel a b k L ha hk hL s r) := by
    rw [expandingDuhamel_eq_intervalIntegral a b k L s ha hk hL hs r,
      ← ContinuousLinearMap.intervalIntegral_comp_comm _
        ((continuousOn_expandingDuhamelIntegrand a b k L ha hk hL s r hr₀).intervalIntegrable_of_Icc hs)]
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le hs] at hτ
    exact (expandingFreeStep_after_kernel a b k L s t ha hk hL hs ht r τ hτ).symm
  have hsecond : (∫ τ in s..s + t, F τ) =
      expandingDuhamel a b k (expandingRadius L s) ha hk
        (hL.trans (expandingRadius_ge L s hL hs)) t (fun u => r (s + u)) := by
    have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := t) F s
    simp only [add_zero] at hshift
    rw [← hshift, expandingDuhamel_eq_intervalIntegral a b k (expandingRadius L s) t ha hk
      (hL.trans (expandingRadius_ge L s hL hs)) ht]
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le ht] at hτ
    exact expanding_shifted_kernel a b k L s t ha hk hL hs r τ hτ
  rw [expandingDuhamel_eq_intervalIntegral a b k L (s + t) ha hk hL (add_nonneg hs ht),
    ← intervalIntegral.integral_add_adjacent_intervals h₁ h₂, hfirst, hsecond]

/-- Restarting a mild trajectory preserves its actual forcing and advances the radius. -/
theorem expandingMild_restart (a b k L s t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 (s + t))) (u₀ : FourierL2) :
    expandingFreeStep a b k L (s + t) ha hk hL (add_nonneg hs ht) u₀ +
      expandingDuhamel a b k L ha hk hL (s + t) r =
    expandingFreeStep a b k (expandingRadius L s) t ha hk
      (hL.trans (expandingRadius_ge L s hL hs)) ht
      (expandingFreeStep a b k L s ha hk hL hs u₀ +
        expandingDuhamel a b k L ha hk hL s r) +
    expandingDuhamel a b k (expandingRadius L s) ha hk
      (hL.trans (expandingRadius_ge L s hL hs)) t (fun u => r (s + u)) := by
  rw [expandingDuhamel_restart a b k L s t ha hk hL hs ht r hr, map_add]
  have h := congrArg (fun A : FourierL2 →L[ℂ] FourierL2 => A u₀)
    (expandingFreeStep_add a b k L s t ha hk hL hs ht)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h]
  abel

end DefocusingNLS

end OAI
