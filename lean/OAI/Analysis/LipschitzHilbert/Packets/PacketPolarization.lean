import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

/-! Exact four-term polarization of a cross packet coefficient and
synthesizing wave. Both packets may have different planar profiles. -/

noncomputable section
namespace LipschitzHilbert

theorem packet_cross_polarization (a b f g : ℂ) :
    (a+b)*(f+g) - (a-b)*(f-g) -
        Complex.I*((a-Complex.I*b)*(f+Complex.I*g)) +
        Complex.I*((a+Complex.I*b)*(f-Complex.I*g)) = 4*(a*g) := by
  ring_nf
  simp [Complex.I_sq]
  ring

theorem packet_cross_polarization_norm (a b f g : ℂ) :
    4*‖a*g‖ ≤ ‖(a+b)*(f+g)‖ + ‖(a-b)*(f-g)‖ +
      ‖(a-Complex.I*b)*(f+Complex.I*g)‖ +
      ‖(a+Complex.I*b)*(f-Complex.I*g)‖ := by
  have hid := packet_cross_polarization a b f g
  have h := calc
    ‖(a+b)*(f+g) - (a-b)*(f-g) -
        Complex.I*((a-Complex.I*b)*(f+Complex.I*g)) +
        Complex.I*((a+Complex.I*b)*(f-Complex.I*g))‖ ≤
      ‖(a+b)*(f+g) - (a-b)*(f-g) -
        Complex.I*((a-Complex.I*b)*(f+Complex.I*g))‖ +
        ‖Complex.I*((a+Complex.I*b)*(f-Complex.I*g))‖ := norm_add_le _ _
    _ ≤ (‖(a+b)*(f+g) - (a-b)*(f-g)‖ +
        ‖Complex.I*((a-Complex.I*b)*(f+Complex.I*g))‖) +
        ‖Complex.I*((a+Complex.I*b)*(f-Complex.I*g))‖ := by
      exact add_le_add
        (norm_sub_le ((a+b)*(f+g) - (a-b)*(f-g))
          (Complex.I*((a-Complex.I*b)*(f+Complex.I*g)))) le_rfl
    _ ≤ (‖(a+b)*(f+g)‖ + ‖(a-b)*(f-g)‖ +
        ‖Complex.I*((a-Complex.I*b)*(f+Complex.I*g))‖) +
        ‖Complex.I*((a+Complex.I*b)*(f-Complex.I*g))‖ := by
      gcongr
      exact norm_sub_le _ _
  rw [hid] at h
  norm_num only [norm_mul,Complex.norm_I,one_mul,Complex.norm_ofNat] at h
  simpa only [norm_mul] using h

end LipschitzHilbert

end

end OAI
