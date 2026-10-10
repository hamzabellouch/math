import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricLocalizedEntry
import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularTightness

namespace OAI

/-! # All bounded histories in a short late-box window use one characteristic core -/

noncomputable section
open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem characteristicHistoryCore_shift {s b R : ℝ} {x c : V}
    {z : ℝ × WeakTime.Phase} (hs : b ≤ s)
    (hz : z ∈ characteristicHistoryCore s R x) :
    z ∈ characteristicHistoryCore b (R+‖x-c‖+6*(s-b)) c := by
  refine ⟨?_,hz.2⟩
  have he : z.2.1+b • z.2.2-c = (z.2.1+s • z.2.2-x)+(x-c)+(b-s) • z.2.2 := by module
  rw [he]
  calc
    _ ≤ ‖z.2.1+s • z.2.2-x‖+‖x-c‖+‖(b-s) • z.2.2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ R+‖x-c‖+6*(s-b) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
      nlinarith [hz.1,mul_le_mul_of_nonneg_left hz.2 (sub_nonneg.mpr hs)]

theorem boundedFlightCone_mem_commonCore {κ d b W s Δ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ ≤ 1) (hd : d ≤ 1/32) (hb : 0 < b)
    (hW : W ≤ κ*b/200) (hs : s ∈ Icc b (b+W)) (hΔ : Δ ≤ W)
    {x v : V} (hp : (x,v) ∈ lateBox κ d s)
    {q : PhysicalFlightState} (hq : boundedFlightCone (Δ,(x,v)) q) :
    flightCharacteristicEquiv (s+Δ) q ∈
      characteristicHistoryCore b (κ*b/4) ((κ*b) • firstAxis) := by
  have hspos : 0 < s := hb.trans_le hs.1
  have hshift := characteristicHistoryCore_shift hs.1
    (c := (κ*b) • firstAxis) (boundedFlightCone_mem_historyCore (t₀ := s) hq)
  refine ⟨hshift.1.trans ?_,hshift.2⟩
  have he : x-(κ*b) • firstAxis = (x-(κ*s) • firstAxis)+(κ*(s-b)) • firstAxis := by module
  have hx : ‖x-(κ*b) • firstAxis‖ ≤ d*κ*s+κ*(s-b) := by
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_smul,axis_norms.1,mul_one,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hκ.le (sub_nonneg.mpr hs.1))]
    exact add_le_add hp.1.le le_rfl
  have hkb : κ*b ≤ b := by nlinarith [mul_le_mul_of_nonneg_right hκsmall hb.le]
  have hst : s ≤ 2*b := by linarith [hs.2]
  have hds : d*κ*s ≤ κ*b/16 := by
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ hspos).le
    nlinarith [mul_le_mul_of_nonneg_left hst hκ.le]
  have hkt : κ*(s-b) ≤ W := by
    have hh := mul_le_mul_of_nonneg_right hκsmall (sub_nonneg.mpr hs.1)
    nlinarith [hs.2]
  nlinarith [hs.2,mul_pos hκ hb]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
