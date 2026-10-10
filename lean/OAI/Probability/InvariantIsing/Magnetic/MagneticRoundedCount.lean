import OAI.Probability.InvariantIsing.Fields.SpinGroupSlice
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! Rounding an interior magnetization to an attainable spin count. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

def magneticRoundedCount (G : ℕ) (s : ℝ) : ℕ := ⌊(G:ℝ)*((1+s)/2)⌋₊

def magneticRoundedValue (G : ℕ) (s : ℝ) : ℝ :=
  if G=0 then s else 2*(magneticRoundedCount G s : ℝ)/G-1

lemma magneticRoundedCount_le (G : ℕ) {s : ℝ} (hs : |s|≤1) :
    magneticRoundedCount G s ≤ G := by
  have h := Nat.floor_le (show 0≤(G:ℝ)*((1+s)/2) by
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [(abs_le.mp hs).1]))
  have ht : (G:ℝ)*((1+s)/2)≤G := by
    nlinarith [(Nat.cast_nonneg G : (0:ℝ)≤G),(abs_le.mp hs).2]
  exact_mod_cast h.trans ht

lemma magneticRoundedCount_value (G : ℕ) {s : ℝ} (_hs : |s|≤1) :
    (magneticRoundedCount G s : ℝ)=(G:ℝ)*((1+magneticRoundedValue G s)/2) := by
  by_cases hG : G=0
  · simp [hG,magneticRoundedCount,magneticRoundedValue]
  · simp only [magneticRoundedValue,ite_eq_right hG]
    have hn : (G:ℝ)≠0 := Nat.cast_ne_zero.mpr hG
    field_simp
    ring

lemma magneticRoundedValue_error {G : ℕ} (hG : 0<G) {s : ℝ} (hs : |s|≤1) :
    |magneticRoundedValue G s-s|≤2/(G:ℝ) := by
  have hp : (0:ℝ)<G := Nat.cast_pos.mpr hG
  have hx : 0≤(G:ℝ)*((1+s)/2) :=
    mul_nonneg hp.le (by linarith [(abs_le.mp hs).1])
  have hl := Nat.floor_le hx
  have hu := Nat.lt_floor_add_one ((G:ℝ)*((1+s)/2))
  have he : magneticRoundedValue G s-s=
      2*((magneticRoundedCount G s : ℝ)-(G:ℝ)*((1+s)/2))/G := by
    simp only [magneticRoundedValue,ite_eq_right (Nat.ne_of_gt hG)]
    field_simp
    ring
  rw [he,abs_div,abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have ha : |(magneticRoundedCount G s : ℝ)-(G:ℝ)*((1+s)/2)|≤1 := by
    apply abs_le.mpr
    dsimp only [magneticRoundedCount]
    constructor <;> linarith
  nlinarith

lemma magneticRoundedValue_tendsto (G : ℕ → ℕ) (hG : Tendsto G atTop atTop)
    {s : ℝ} (hs : |s|≤1) :
    Tendsto (fun k => magneticRoundedValue (G k) s) atTop (𝓝 s) := by
  have hpos : ∀ᶠ k in atTop, 0<G k := hG.eventually (eventually_gt_atTop 0)
  have he : Tendsto (fun k => 2/(G k : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hG))
  have hzero : Tendsto (fun k => magneticRoundedValue (G k) s-s) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ he
    · filter_upwards [hpos] with k hk
      simpa only [Real.norm_eq_abs] using magneticRoundedValue_error hk hs
  simpa only [sub_add_cancel,zero_add] using hzero.add_const s

end InvariantIsing

end

end OAI
