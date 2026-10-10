import OAI.MeasureTheory.Falconer.Radial.ScalarAffineCovers

namespace OAI

/-! Exact ball transfer through the fixed scalar zoom into the unit interval. -/
namespace Falconer

 theorem scalar_zoom_ball_bound {δ R K s : ℝ} (hδ : 0 < δ) (hR : 1 ≤ R)
    (hK : 1 ≤ K) (hs : 0 ≤ s) (z : ℝ) (X : Finset ℝ)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ K*r^s*(X.card:ℝ)) :
    ∀ u r : ℝ, δ/R ≤ r → r ≤ 1 → scalarBallMass (scalarZoom z R X) u r ≤
      (R^s*K)*r^s*((scalarZoom z R X).card:ℝ) := by
  have hR0 : 0 < R := by linarith
  intro u r hr _
  have hr0 : 0 < r := (div_pos hδ hR0).trans_le hr
  rw [scalarZoom_ball_mass hR0,scalarZoom_card hR0.ne']
  by_cases hsmall : R*r ≤ 1
  · have hδr : δ ≤ R*r := by
      have hh := (div_le_iff₀ hR0).1 hr
      nlinarith
    have hh := hball (z+R*u) (R*r) hδr hsmall
    rw [Real.mul_rpow hR0.le hr0.le] at hh
    nlinarith
  · have hcount : scalarBallMass X (z+R*u) (R*r) ≤ (X.card:ℝ) := by
      unfold scalarBallMass
      exact_mod_cast Finset.card_filter_le _ _
    have hp : 1 ≤ (R*r)^s := Real.one_le_rpow (le_of_not_ge hsmall) hs
    rw [Real.mul_rpow hR0.le hr0.le] at hp
    have hfactor : 1 ≤ R^s*K*r^s := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg X.card)
    nlinarith

 theorem scalar_quarter_zoom_unit (X : Finset ℝ) (hX : ∀ x ∈ X, |x| ≤ 1) :
    ∀ y ∈ scalarZoom (-2) 4 X, 0 ≤ y ∧ y < 1 := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  have hh := abs_le.mp (hX x hx)
  constructor <;> linarith

end Falconer

end OAI
