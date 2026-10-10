import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFiniteContinuity

namespace OAI

/-! Equality on an outgoing tail propagates back to the matching radius. -/

open Set Filter
namespace DefocusingNLS

theorem radialExterior_terminal_unique (ν : ℂ) (n : ℕ) (L U : ℝ)
    (Z W : ℝ → ℂ × ℂ) (hcZ : Continuous Z) (hcW : Continuous W)
    (hZ : ∀ t ∈ Icc L U, HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t)
    (hW : ∀ t ∈ Icc L U, HasDerivAt W (radialExteriorODEField ν n t (W t)) t)
    (he : Z U=W U) (t : ℝ) (ht : t ∈ Icc L U) : Z t=W t := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc L U)).exists_bound_of_continuousOn hcZ.continuousOn
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Icc L U)).exists_bound_of_continuousOn hcW.continuousOn
  let ρ := max C D
  have hρ : 0 ≤ ρ := (norm_nonneg (Z t)).trans ((hC t ht).trans (le_max_left _ _))
  have hT : 0 ≤ U-L := sub_nonneg.mpr (ht.1.trans ht.2)
  have hdZ : ∀ (_i : ℕ) (s : ℝ), s ∈ Icc (U-(U-L)) U → HasDerivAt (fun r => Z r)
      (radialExteriorFiniteField ν n (fun _ => 0) ρ s (Z s)) s := by
    intro _ s hs
    have hs' : s ∈ Icc L U := by simpa only [sub_sub_cancel] using hs
    rw [radialExteriorFiniteField_eq ν n (fun _ => 0) ρ s (Z s) (by
      simpa only [sub_zero] using (norm_fst_le (Z s)).trans ((hC s hs').trans (le_max_left _ _)))]
    exact hZ s hs'
  have hdW : ∀ s ∈ Icc (U-(U-L)) U, HasDerivAt W
      (radialExteriorFiniteField ν n (fun _ => 0) ρ s (W s)) s := by
    intro s hs
    have hs' : s ∈ Icc L U := by simpa only [sub_sub_cancel] using hs
    rw [radialExteriorFiniteField_eq ν n (fun _ => 0) ρ s (W s) (by
      simpa only [sub_zero] using (norm_fst_le (W s)).trans ((hD s hs').trans (le_max_right _ _)))]
    exact hW s hs'
  have hx : Tendsto (fun _ : ℕ => Z U) atTop (nhds (W U)) := by
    rw [he]
    exact tendsto_const_nhds
  have hconv := radialExterior_finite_parameter_limit n (fun _ : ℕ => ν) ν tendsto_const_nhds
    (fun _ => 0) continuous_const ρ (2*ρ) U (U-L) hρ hT
    (fun _ _ => by simp) (fun _ : ℕ => Z) W (fun _ => hcZ) hcW hdZ hdW hx
  have hlim : Tendsto (fun _ : ℕ => Z t) atTop (nhds (W t)) :=
    hconv.tendsto_at (by simpa only [sub_sub_cancel] using ht)
  exact tendsto_nhds_unique tendsto_const_nhds hlim

theorem radialExterior_outgoing_unique (ν : ℂ) (n : ℕ) (m : ℂ) (L : ℝ)
    (Z W : ℝ → ℂ × ℂ) (hcZ : Continuous Z) (hcW : Continuous W)
    (hZ : ∀ t, L ≤ t → HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t)
    (hW : ∀ t, L ≤ t → HasDerivAt W (radialExteriorODEField ν n t (W t)) t)
    (heZ : HasRadialOutgoingExpansion ν n m Z)
    (heW : HasRadialOutgoingExpansion ν n m W)
    (t : ℝ) (ht : L ≤ t) : Z t=W t := by
  have he := radialExterior_outgoing_eventually_eq ν n m Z W L hZ hW heZ heW
  obtain ⟨U,hU⟩ := ((eventually_ge_atTop t).and he).exists
  exact radialExterior_terminal_unique ν n L U Z W hcZ hcW
    (fun s hs => hZ s hs.1) (fun s hs => hW s hs.1) hU.2 t ⟨ht,hU.1⟩

end DefocusingNLS

end OAI
