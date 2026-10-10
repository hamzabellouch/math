import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedMeshStep

namespace OAI

/-! # A uniform positive first-collision weight into the beam neighborhood -/

noncomputable section

open MeasureTheory Set Metric NormedSpace
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_near_partner_lower {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (v w e : V) (hw : ‖w‖ ≤ 2) (hv : ‖v‖ ≤ R) (hne : v ≠ w)
    (hwe : dist w e ≤ δ/2) :
    ENNReal.ofReal (sphereCapMass (δ/(R+2))) ≤ outgoing (v,w) (ball e δ) := by
  let n : Sphere := ⟨-normalize (v-w),mem_sphere_zero_iff_norm.mpr
    (by rw [norm_neg,norm_normalize (sub_ne_zero.mpr hne)])⟩
  have hn : child v w n.1 = w := (child_normalized_endpoints v w).2
  have hh := outgoing_bounded_endpoint_cap hR hδ v w e hw hv n (by rw [hn]; exact hwe)
  exact (ENNReal.ofReal_le_ofReal hh).trans ENNReal.ofReal_toReal_le

def firstEntryMass (R δ c : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (3*Real.pi*c)*ENNReal.ofReal (sphereCapMass (δ/(R+2)))

theorem firstEntryMass_pos {R δ c : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hc : 0 < c) :
    0 < firstEntryMass R δ c := by
  apply pos_iff_ne_zero.mpr
  exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sphereCapMass_pos (div_pos hδ (by linarith)))))

theorem firstEntryMass_lower {R δ c b : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hc : 0 < c) (hb : c ≤ b) {v w e : V} (hw : ‖w‖ ≤ 2) (hv : ‖v‖ ≤ R)
    (hvw : 3/4 ≤ ‖v-w‖) (hwe : dist w e ≤ δ/2) :
    firstEntryMass R δ c ≤
      ENNReal.ofReal (4*Real.pi*b*‖v-w‖)*outgoing (v,w) (ball e δ) := by
  have hne : v ≠ w := by
    intro h
    rw [h,sub_self,norm_zero] at hvw
    norm_num at hvw
  have hb0 : 0 ≤ b := hc.le.trans hb
  have hrate : 3*Real.pi*c ≤ 4*Real.pi*b*‖v-w‖ := by
    calc
      _ = 4*Real.pi*c*(3/4) := by ring
      _ ≤ 4*Real.pi*b*(3/4) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hvw (by positivity)
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hrate)
    (outgoing_near_partner_lower hR hδ v w e hw hv hne hwe)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
