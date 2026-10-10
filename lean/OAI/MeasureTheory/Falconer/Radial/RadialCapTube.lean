import OAI.MeasureTheory.Falconer.Radial.RadialFreezing

namespace OAI

/-! # Final radial caps put entire hit children in a witness's physical tube -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_cap_child_tube (x z q y u : E) {r D B : ℝ}
    (hq : q ≠ x) (hB : ‖z-x‖ ≤ B)
    (hzcap : ‖normalize (z-x)-u‖ ≤ r) (hqcap : ‖normalize (q-x)-u‖ ≤ r)
    (hy : ‖y-z‖ ≤ D) :
    ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D+2*B*r := by
  let v := normalize (z-x)
  let w := normalize (q-x)
  have hw : ‖w‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hr : 0 ≤ r := (norm_nonneg _).trans hzcap
  have hclose : ‖v-w‖ ≤ 2*r := by
    have hh := norm_sub_le_norm_sub_add_norm_sub v u w
    rw [norm_sub_rev u w] at hh
    exact hh.trans (by change _ ≤ 2*r; linarith)
  have hww : perpendicularPart w w = 0 := by simp [perpendicularPart,hw]
  have hv : ‖perpendicularPart w v‖ ≤ 2*r := by
    have hh := norm_perpendicularPart_le hw (v-w)
    rw [perpendicularPart_sub,hww,sub_zero] at hh
    exact hh.trans hclose
  have hzline : ‖perpendicularPart w (z-x)‖ ≤ B*(2*r) := by
    have he : z-x = ‖z-x‖ • v := (norm_smul_normalize (z-x)).symm
    rw [he,perpendicularPart_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul hB hv (norm_nonneg _) hB0
  have he : perpendicularPart w (y-x) = perpendicularPart w (y-z)+perpendicularPart w (z-x) := by
    simp only [perpendicularPart,inner_sub_right,sub_smul]
    abel
  change ‖perpendicularPart w (y-x)‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add ((norm_perpendicularPart_le hw _).trans hy) hzline).trans_eq (by ring))

end Falconer

end OAI
