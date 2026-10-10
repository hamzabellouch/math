import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Backward uniqueness on a finite radial annulus, used for regular spectral columns. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectral_zero_on_annulus (Z Z' : ℝ → E₄) (L R B : ℝ)
    (hZ : ContinuousOn Z (Icc L R))
    (hD : ∀ r ∈ Icc L R, HasDerivAt Z (Z' r) r)
    (hB : ∀ r ∈ Icc L R, ‖Z' r‖ ≤ B*‖Z r‖)
    (hz : Z R=0) (r : ℝ) (hr : r ∈ Icc L R) : Z r=0 := by
  let V : ℝ → E₄ := fun t => Z (R-t)
  let V' : ℝ → E₄ := fun t => -Z' (R-t)
  have hmem (t : ℝ) (ht : t ∈ Icc 0 (R-r)) : R-t ∈ Icc L R := by
    constructor <;> linarith [hr.1,ht.1,ht.2]
  have hc : ContinuousOn V (Icc 0 (R-r)) := hZ.comp
    (continuous_const.sub continuous_id).continuousOn hmem
  have hd : ∀ t ∈ Ico 0 (R-r), HasDerivWithinAt V (V' t) (Ici t) t := by
    intro t ht
    have hh := (hD (R-t) (hmem t ⟨ht.1,ht.2.le⟩)).scomp t ((hasDerivAt_id t).const_sub R)
    simpa only [V,V',Function.comp_def,neg_one_smul] using! hh.hasDerivWithinAt
  have hb : ∀ t ∈ Ico 0 (R-r), ‖V' t‖ ≤ B*‖V t‖+0 := by
    intro t ht
    simpa only [V,V',norm_neg,add_zero] using hB (R-t) (hmem t ⟨ht.1,ht.2.le⟩)
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hc hd
    (show ‖V 0‖ ≤ 0 by simp [V,hz]) hb (R-r) ⟨by linarith [hr.2],le_rfl⟩
  have he : gronwallBound 0 B 0 (R-r)=0 := by
    by_cases hB0 : B=0 <;> simp [gronwallBound,hB0]
  rw [sub_zero,he] at h
  apply norm_le_zero_iff.mp
  simpa only [V,sub_sub_cancel] using h

end DefocusingNLS

end OAI
