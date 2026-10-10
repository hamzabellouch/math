import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! The normalized coordinates and support geometry in the packet
representation of the annular band multiplier (§2). -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def symbolX (l xi eta theta : ℝ) : ℝ := l*(xi+theta*eta)
def symbolY (W eta center : ℝ) : ℝ := W*(eta-center)
def symbolU (l w u theta : ℝ) : ℝ := (u-theta)/(w/l)

theorem normalized_symbol_identity (l w xi eta theta u : ℝ) (hl : l≠0) (hw : w≠0) :
    l*(xi+u*eta)=symbolX l xi eta theta+(w*eta)*symbolU l w u theta := by
  unfold symbolX symbolU
  field_simp
  ring

theorem normalized_vertical_identity (m w eta center : ℝ) (hm : m≠0) :
    w*eta=w*center+symbolY (m*w) eta center/m := by
  unfold symbolY
  field_simp
  ring

/-- The annular multiplier and the narrow horizontal frequency support
force the normalized selector away from zero, uniformly in the scales. -/
theorem normalized_selector_lower (X V U c C : ℝ)
    (_hc : 0<c) (hC : 0<C) (hV0 : 0≤V) (hV : V≤C)
    (hX : |X|≤c/4) (hAnnulus : c≤|X+V*U|) :
    3*c/(4*C)≤|U| := by
  have hm : |V*U|=V*|U| := by rw [abs_mul, abs_of_nonneg hV0]
  have htri := abs_add_le X (V*U)
  have hbound : V*|U|≤C*|U| := mul_le_mul_of_nonneg_right hV (abs_nonneg U)
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hC)).2
  nlinarith only [hX,hAnnulus,htri,hm,hbound]

/-- The positive vertical annulus also bounds the normalized selector
above; no scale or bin count enters the bound. -/
theorem normalized_selector_upper (X V U c C M : ℝ)
    (hc : 0<c) (hV : c≤V) (hX : |X|≤C/4) (hAnnulus : |X+V*U|≤M) :
    |U|≤(M+C/4)/c := by
  have hV0 : 0≤V := hc.le.trans hV
  have hm : |V*U|=V*|U| := by rw [abs_mul, abs_of_nonneg hV0]
  have htri : |V*U|≤|X+V*U|+|X| := by
    calc
      _ = |(X+V*U)+(-X)| := by congr 1; ring
      _ ≤ |X+V*U|+|-X| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hbound : c*|U|≤V*|U| := mul_le_mul_of_nonneg_right hV (abs_nonneg U)
  apply (le_div_iff₀ hc).2
  nlinarith only [hX,hAnnulus,htri,hm,hbound]

theorem bounded_contributing_slope (u theta d U M : ℝ)
    (hu : |u|≤1) (hd0 : 0≤d) (hd1 : d≤1) (hU : |U|≤M)
    (hcoord : u-theta=d*U) : |theta|≤1+M := by
  have htheta : theta=u-d*U := by linarith only [hcoord]
  rw [htheta]
  have hmul : |d*U|≤M := by
    rw [abs_mul, abs_of_nonneg hd0]
    exact (mul_le_mul_of_nonneg_right hd1 (abs_nonneg U)).trans (by simpa using hU)
  have ht : |u-d*U|≤|u|+|d*U| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le u (-(d*U))
  exact ht.trans (add_le_add hu hmul)

/-- The wave slopes stay in a fixed multiple of the angular scale
around the lattice label. -/
theorem frequency_slope_margin (l w xi eta theta c C : ℝ)
    (hl : 0<l) (hw : 0<w) (hc : 0<c) (hC : 0≤C)
    (hV : c≤w*eta) (hX : |symbolX l xi eta theta|≤C) :
    |(-xi/eta)-theta|≤(C/c)*(w/l) := by
  have heta : 0<eta := pos_of_mul_pos_right (hc.trans_le hV) hw.le
  have hscale : |(-xi/eta)-theta|=|symbolX l xi eta theta|/(l*eta) := by
    unfold symbolX
    rw [abs_mul, abs_of_pos hl]
    have hid : -xi/eta-theta=-(xi+theta*eta)/eta := by field_simp; ring
    rw [hid, abs_div, abs_neg, abs_of_pos heta]
    field_simp
  rw [hscale]
  apply (div_le_iff₀ (mul_pos hl heta)).2
  calc
    _ ≤ C := hX
    _ ≤ (C/c)*(w/l)*(l*eta) := by
      have hb : C≤(C/c)*(w*eta) := by
        calc
          C = (C/c)*c := by field_simp
          _ ≤ (C/c)*(w*eta) := mul_le_mul_of_nonneg_left hV (div_nonneg hC hc.le)
      convert hb using 1; field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
