import OAI.Analysis.PlanarPacking.Entire
import OAI.Analysis.PlanarPacking.BarrierProduct

namespace OAI

namespace SharpPlanar
open Set
lemma P_period (s : ℝ) : P (s+12) = P s := by
  simp only [P_cos_factor, show Real.pi*(s+12-2)/6 = Real.pi*(s-2)/6 + 2*Real.pi by ring,
    Real.cos_add_two_pi]
lemma P_reflect (s : ℝ) : P (4-s) = P s := by
  simp only [P_cos_factor, show Real.pi*(4-s-2)/6 = -(Real.pi*(s-2)/6) by ring,
    Real.cos_neg]
lemma P_half : P (1/2) = 3-2*Real.sqrt 2 := by
  rw [P_cos_factor,show Real.pi*((1/2:ℝ)-2)/6 = -(Real.pi/4) by ring,
    Real.cos_neg,Real.cos_pi_div_four]
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have he : 4*(Real.sqrt 2/2)^2-3 = (-1:ℝ) := by nlinarith
  rw [he]
  nlinarith
lemma P_two : P 2 = 1 := by norm_num [P_cos_factor]
lemma P_eight : P 8 = 9 := by
  rw [P_cos_factor,show Real.pi*((8:ℝ)-2)/6 = Real.pi by ring,Real.cos_pi]
  norm_num
lemma P_short_lower : (17/100:ℝ) < P (1/2) := by
  rw [P_half]
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hb : Real.sqrt 2 < 283/200 := by nlinarith
  linarith
lemma P_long_lower : (4:ℝ) ≤ P (11/2) := by
  rw [P_cos_factor]
  have ha : Real.pi*((11/2:ℝ)-2)/6 = 7*Real.pi/12 := by ring
  rw [ha]
  have hc1 : Real.cos (7*Real.pi/12) ≤ 0 := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi/2)
      (by linarith [Real.pi_pos] : 7*Real.pi/12 ≤ Real.pi)
      (by linarith [Real.pi_pos] : Real.pi/2 ≤ 7*Real.pi/12)
    simpa using hh
  have hc2 : -(1/2:ℝ) ≤ Real.cos (7*Real.pi/12) := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ 7*Real.pi/12)
      (by linarith [Real.pi_pos] : 2*Real.pi/3 ≤ Real.pi)
      (by linarith [Real.pi_pos] : 7*Real.pi/12 ≤ 2*Real.pi/3)
    have he : Real.cos (2*Real.pi/3) = -(1/2:ℝ) := by
      rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three]
    rwa [he] at hh
  have hsq : Real.cos (7*Real.pi/12)^2 ≤ 1/4 := by nlinarith
  have h1 : (4*Real.cos (7*Real.pi/12)^2-3)^2 ≥ 4 := by nlinarith [sq_nonneg (Real.cos (7*Real.pi/12))]
  have h2 : (1-2*Real.cos (7*Real.pi/12))^2 ≥ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
lemma P_other_midpoints : P (7/2) = P (1/2) ∧ P (21/2) = P (11/2) ∧ P (-3/2) = P (11/2) := by
  constructor
  · convert P_reflect (1/2) using 1; congr 1; norm_num
  constructor
  · have hp := P_period (-(3/2))
    have hr := P_reflect (11/2)
    norm_num at hp hr
    exact hp.trans hr
  · convert P_reflect (11/2) using 1; congr 1; norm_num

lemma barrier_endpoints (a : ℕ) (ha : a ∈ residues) :
    (17/25:ℝ) ≤ dividedP a (-leftHalf a) ∧ (17/25:ℝ) ≤ dividedP a (rightHalf a) := by
  have hl := dividedP_factor a ha (-leftHalf a)
  have hr := dividedP_factor a ha (rightHalf a)
  have hs := P_short_lower
  have ht := P_two
  have he := P_eight
  have hg := P_long_lower
  have hm := P_other_midpoints
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [leftHalf,rightHalf] at hl hr ⊢ <;>
    norm_num at hm <;> constructor <;> nlinarith [hm.1,hm.2.1,hm.2.2]
end SharpPlanar

end OAI
