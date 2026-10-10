import Mathlib.Analysis.Complex.AbsMax

namespace OAI

/-! A bounded holomorphic disk-valued limit is interior everywhere once it
is interior at one point of the connected domain. -/
noncomputable section
open Set Function

namespace SLEExactGauge

lemma holomorphic_disk_strict_of_point {D : Set ℂ} (hD : IsOpen D)
    (hconn : IsPreconnected D) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D)
    (hbound : ∀ z∈D, ‖F z‖≤1) {a : ℂ} (ha : a∈D) (hFa : ‖F a‖<1) :
    ∀ z∈D, ‖F z‖<1 := by
  intro z hz
  by_contra hnot
  have he : ‖F z‖=1 := le_antisymm (hbound z hz) (le_of_not_gt hnot)
  have hmax : IsMaxOn (norm ∘ F) D z := by
    intro w hw
    change ‖F w‖≤‖F z‖
    rw [he]
    exact hbound w hw
  have hh := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hconn hD hF hz hmax ha
  have hnorm : ‖F a‖=‖F z‖ := hh
  exact hFa.ne (hnorm.trans he)

end SLEExactGauge

end

end OAI
