import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeODEUniqueness

namespace OAI

/-! A free physical solution is determined on the whole exterior by any terminal collar. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFree_eq_on_open_of_collar (b ζ η : ℂ) (X Y : ℝ → E₄)
    (L δ R : ℝ) (hL : 0 < L) (_hLδ : L < δ) (hδR : δ < R)
    (hX : ∀ r ∈ Ioo L R, HasDerivAt X (spectralFreePhysicalPairField b ζ η r (X r)) r)
    (hY : ∀ r ∈ Ioo L R, HasDerivAt Y (spectralFreePhysicalPairField b ζ η r (Y r)) r)
    (he : EqOn X Y (Ioo δ R)) : EqOn X Y (Ioo L R) := by
  intro r hr
  by_cases hδr : δ < r
  · exact he ⟨hδr,hr.2⟩
  · let t := (δ+R)/2
    have hδt : δ < t := by dsimp [t]; linarith
    have htR : t < R := by dsimp [t]; linarith
    have hrt : r < t := (le_of_not_gt hδr).trans_lt hδt
    have hsub : Icc r t ⊆ Ioo L R := fun x hx =>
      ⟨hr.1.trans_le hx.1,hx.2.trans_lt htR⟩
    have hXc : ContinuousOn X (Icc r t) := fun x hx =>
      (hX x (hsub hx)).continuousAt.continuousWithinAt
    have hYc : ContinuousOn Y (Icc r t) := fun x hx =>
      (hY x (hsub hx)).continuousAt.continuousWithinAt
    exact spectralFree_eq_on_annulus b ζ η X Y r t (hL.trans hr.1) hrt hXc hYc
      (fun x hx => hX x (hsub ⟨hx.1.le,hx.2.le⟩))
      (fun x hx => hY x (hsub ⟨hx.1.le,hx.2.le⟩))
      (he ⟨hδt,htR⟩) ⟨le_rfl,hrt.le⟩

end DefocusingNLS

end OAI
