import OAI.Analysis.StrictMeans.BoxTransport

namespace OAI

section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace StrictInverseFirstPower
noncomputable section

lemma slope_le_of_all_positive {a b c : ℝ}
    (h : ∀ S : ℝ, 0 < S → S*a ≤ S*b+c) : a ≤ b := by
  by_contra hn
  have hp : 0 < a-b := sub_pos.mpr (lt_of_not_ge hn)
  let S := (|c|+1)/(a-b)
  have hS : 0 < S := div_pos (by positivity) hp
  have he : S*(a-b)=|c|+1 := div_mul_cancel₀ _ hp.ne'
  have hh := h S hS
  nlinarith [le_abs_self c]

lemma ennreal_box_slope {A d : ℝ≥0∞} (hd : d≠⊤) {N : ℝ} (hN : 1 ≤ N)
    (h : ∀ S Y : ℝ, 0 < S → 1 < Y →
      ENNReal.ofReal (2*S*Real.log Y)*A ≤
        ENNReal.ofReal (2*(S+N*Y)*(Real.log Y+2*Real.log N))*d) : A ≤ d := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hA : A ≠ ⊤ := by
    have hh := h 1 (Real.exp 1) zero_lt_one (Real.one_lt_exp_iff.mpr zero_lt_one)
    simp only [mul_one,Real.log_exp] at hh
    have hfin : ENNReal.ofReal (2 * (1+N*Real.exp 1)*(1+2*Real.log N))*d < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hd)
    have hx := hh.trans_lt hfin
    intro ha
    rw [ha,ENNReal.mul_top (by norm_num)] at hx
    exact (lt_irrefl ⊤) hx
  apply (ENNReal.toReal_le_toReal hA hd).mp
  apply slope_le_of_all_positive (c := 2*Real.log N*d.toReal)
  intro t ht
  have hin (S : ℝ) (hS : 0 < S) := h S (Real.exp t) hS (Real.one_lt_exp_iff.mpr ht)
  have hlin : t*A.toReal ≤ (t+2*Real.log N)*d.toReal := by
    apply slope_le_of_all_positive (c := N*Real.exp t*(t+2*Real.log N)*d.toReal)
    intro S hS
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd) (hin S hS)
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul] at hh
    simp only [Real.log_exp] at hh
    rw [ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (by positivity)] at hh
    nlinarith
  nlinarith

end
end StrictInverseFirstPower

end

end OAI
