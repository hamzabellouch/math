import OAI.Geometry.RCD.Heat.GaussianScaleAbsorption

namespace OAI

/-! # The normalization exponential is absorbed by the two Gaussian tails -/

open Set Filter
noncomputable section
namespace RegularPointCoordinates

theorem gaussian_bridge_exponent {c s t d E : ℝ}
    (hc : 0 < c) (hs : 0 < s) (ht : 0 < t) (hsc : s ≤ c) (htc : t ≤ c)
    (hE : 20*E ≤ d^2) :
    -d^2/(20*s)+ -d^2/(20*t)+E/c  ≤  -d^2/(40*s)+ -d^2/(40*t) := by
  have hbudget : E/c  ≤  d^2/(40*s)+d^2/(40*t) := by
    calc
      E/c  ≤  (d^2/20)/c := div_le_div_of_nonneg_right (by linarith) hc.le
      _ = (d^2/40)*(1/c)+(d^2/40)*(1/c) := by ring
      _  ≤  (d^2/40)*(1/s)+(d^2/40)*(1/t) :=
        add_le_add (mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hs hsc) (by positivity))
          (mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le ht htc) (by positivity))
      _ = _ := by ring
  have hspl : d^2/(20*s)=2*(d^2/(40*s)) := by ring
  have htpl : d^2/(20*t)=2*(d^2/(40*t)) := by ring
  simp only [neg_div,hspl,htpl]
  linarith

theorem gaussian_bridge_tail (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {c s t d E : ℝ}, 0 < c → c ≤ 1 → 0 < s → 0 < t →
      s ≤ c → t ≤ c → 1 ≤ d → 20*E ≤ d^2 →
      ((Real.sqrt s)⁻¹^n*Real.exp (-d^2/(20*s)))*
        ((Real.sqrt t)⁻¹^n*Real.exp (-d^2/(20*t)))*Real.exp (E/c)  ≤
          C^2*Real.exp (-d^2/40) := by
  obtain ⟨C,hC,hshort⟩ := exists_gaussian_short_time_bound n (show (0:ℝ) < 40 by norm_num)
  refine ⟨C,hC,?_⟩
  intro c s t d E hc hc1 hs ht hsc htc hd hE
  have hsb := hshort 1 s d (by norm_num) hs (by simpa only [one_pow] using hsc.trans hc1) hd
  have htb := hshort 1 t d (by norm_num) ht (by simpa only [one_pow] using htc.trans hc1) hd
  norm_num only [one_pow,inv_one,mul_one,one_mul,show (2:ℝ)*40=80 by norm_num] at hsb htb
  let P := (Real.sqrt s)⁻¹^n*(Real.sqrt t)⁻¹^n
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  calc
    _ = P*Real.exp (-d^2/(20*s)+ -d^2/(20*t)+E/c) := by
      rw [Real.exp_add,Real.exp_add]
      dsimp only [P]
      ring
    _  ≤  P*Real.exp (-d^2/(40*s)+ -d^2/(40*t)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (gaussian_bridge_exponent hc hs ht hsc htc hE)) hP
    _ = ((Real.sqrt s)⁻¹^n*Real.exp (-d^2/(40*s)))*
        ((Real.sqrt t)⁻¹^n*Real.exp (-d^2/(40*t))) := by
      rw [Real.exp_add]
      dsimp only [P]
      ring
    _  ≤  (C*Real.exp (-d^2/80))*(C*Real.exp (-d^2/80)) :=
      mul_le_mul hsb htb (by positivity) (by positivity)
    _ = C^2*Real.exp (-d^2/40) := by
      rw [show -d^2/40 = -d^2/80+ -d^2/80 by ring,Real.exp_add]
      ring

end RegularPointCoordinates

end

end OAI
