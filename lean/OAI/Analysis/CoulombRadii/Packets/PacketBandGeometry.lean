import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PacketWidthScalar

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

lemma packet_band_center_support {g : Position → ℝ}
    (hg : ∀ z,1 < ‖z‖ → g z=0) {c r₀ s r L : ℝ}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hr : 0 < r)
    (hL : 1 ≤ L) (hr₀r : r₀ ≤ r)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/4)
    (hwidth : c*s^packetExponent ≤ 1/100)
    {y : Position} (hy0 : r/2 ≤ ‖y‖) (hy1 : ‖y‖ ≤ 8*L*r)
    {x : Position} (hK : packetKernel g c r₀ s x y ≠ 0) :
    r/3 ≤ ‖x‖ ∧ ‖x‖ ≤ 10*L*r := by
  have hsp := packetKernel_support g hg hc hr₀ hs x y hK
  have ht := packetWidth_lipschitz hc.le hr₀ hs x y
  have hn : ‖y-x‖=‖x-y‖ := norm_sub_rev _ _
  have he : packetWidth c r₀ s x-packetWidth c r₀ s y ≤ ‖y-x‖/4 := by
    apply (le_abs_self _).trans
    apply ht.trans
    rw [←hn]
    have hh := mul_le_mul_of_nonneg_right hscale (norm_nonneg (y-x))
    linarith
  have hp := packetWidth_le c r₀ s hc.le hr₀ hs y
  have hxmax : max ‖y‖ r₀ ≤ 2*‖y‖ := max_le (by linarith [norm_nonneg y]) (by linarith)
  have hsize : packetWidth c r₀ s y ≤ ‖y‖/50 := by
    calc
      _ ≤ (c*s^packetExponent)*max ‖y‖ r₀ := hp
      _ ≤ (1/100)*(2*‖y‖) := mul_le_mul hwidth hxmax
        (le_max_of_le_left (norm_nonneg y)) (by norm_num)
      _ = _ := by ring
  have hdist : ‖y-x‖ ≤ ‖y‖/25 := by linarith
  have hny := norm_le_norm_add_norm_sub y x
  have hnx := norm_le_norm_add_norm_sub x y
  rw [←hn] at hnx
  constructor
  · nlinarith
  · calc
      ‖x‖ ≤ (26/25:ℝ)*‖y‖ := by linarith
      _ ≤ (26/25:ℝ)*(8*L*r) := mul_le_mul_of_nonneg_left hy1 (by norm_num)
      _ ≤ 10*L*r := by
        nlinarith only [mul_nonneg (zero_le_one.trans hL) hr.le]

lemma packet_band_width_lower {c r₀ s r : ℝ}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hr : 0 < r) (hrs : r ≤ s)
    {x : Position} (hx : r/3 ≤ ‖x‖) :
    c*(r/3)*(r/3)^packetExponent ≤ packetWidth c r₀ s x := by
  have hmax : r/3 ≤ max ‖x‖ r₀ := hx.trans (le_max_left _ _)
  have hm : r/3 ≤ min (max ‖x‖ r₀) s := le_min hmax (by linarith)
  unfold packetWidth
  exact mul_le_mul (mul_le_mul_of_nonneg_left hmax hc.le)
    (Real.rpow_le_rpow (by positivity) hm (by norm_num [packetExponent]))
    (Real.rpow_nonneg (by positivity) _) (by positivity)

lemma packet_band_observation_support {r L d : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hd : d ≤ r/12)
    {x y : Position} (hx : r/3 ≤ ‖x‖ ∧ ‖x‖ ≤ 10*L*r)
    (hdist : ‖x-y‖ ≤ d) : r/4 ≤ ‖y‖ ∧ ‖y‖ ≤ 12*L*r := by
  have hx' := norm_le_norm_add_norm_sub x y
  have hy' := norm_le_norm_add_norm_sub y x
  rw [norm_sub_rev y x] at hy'
  have hrL := mul_le_mul_of_nonneg_right hL hr.le
  constructor <;> nlinarith
end NeutralAtom
end

end

end OAI
