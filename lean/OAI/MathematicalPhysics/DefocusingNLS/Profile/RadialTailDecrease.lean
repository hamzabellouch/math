import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialNoReturn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-! The positive free tail is strictly decreasing after leaving the core. -/

open Set
namespace DefocusingNLS

theorem radial_free_tail_decreasing (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R)
    (A D V : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hAN : ∀ r ∈ Ioo ρ R, 0 < A r) (hVN : ∀ r ∈ Ioo ρ R, 0 < V r)
    (hAD : ∀ r ∈ Ioo ρ R, HasDerivAt A (D r) r)
    (hDE : ∀ r ∈ Ioo ρ R, HasDerivAt D (-11/r*D r-V r*A r) r)
    (hDρ : D ρ=0) :
    (∀ r ∈ Ioo ρ R, D r < 0) ∧ StrictAntiOn A (Icc ρ R) := by
  let F := fun r : ℝ => r^11*D r
  have hF : ∀ r ∈ Ioo ρ R, HasDerivAt F (-(r^11*V r*A r)) r := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt (hρ.trans hr.1)
    convert! ((hasDerivAt_id r).pow 11).mul (hDE r hr) using 1
    simp only [Pi.pow_apply,id_eq,mul_one]
    field_simp [hr0]
    ring
  have hFA : StrictAntiOn F (Icc ρ R) :=
    strictAntiOn_of_deriv_neg (convex_Icc ρ R)
      ((continuous_id.pow 11).mul hD).continuousOn (by
        intro r hr
        rw [interior_Icc] at hr
        rw [(hF r hr).deriv]
        exact neg_lt_zero.mpr (mul_pos (mul_pos (pow_pos (hρ.trans hr.1) 11) (hVN r hr)) (hAN r hr)))
  have hDn : ∀ r ∈ Ioo ρ R, D r < 0 := by
    intro r hr
    have hlt := hFA (show ρ ∈ Icc ρ R from ⟨le_rfl,hρR.le⟩) ⟨hr.1.le,hr.2.le⟩ hr.1
    change r^11*D r < ρ^11*D ρ at hlt
    rw [hDρ,mul_zero] at hlt
    have hp : 0 < r^11 := pow_pos (hρ.trans hr.1) 11
    nlinarith
  refine ⟨hDn,strictAntiOn_of_deriv_neg (convex_Icc ρ R) hA.continuousOn ?_⟩
  intro r hr
  rw [interior_Icc] at hr
  rw [(hAD r hr).deriv]
  exact hDn r hr

end DefocusingNLS

end OAI
