import OAI.NumberTheory.TotientAsymptotic.CoarseTotientBounds

namespace OAI

/-! Pointwise value-counting bounds from the finite dyadic envelope. -/
noncomputable section
namespace TotientAsymptotic

lemma dyadic_value_count_bound {N J : ℕ} (hN : 2 ≤ N) (hNJ : N ≤ 2^J) :
    V N ≤ 2*dyadicTotientEnvelope J*N/Real.log N := by
  let k := Nat.clog 2 N
  have hb := dyadic_nat_bounds (by omega : 1 < N)
  have hk : 1 ≤ k := hb.1
  have hkJ : k ≤ J := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hNJ
  have hNpow : (N:ℝ) ≤ (2:ℝ)^k := hb.2.2
  have hpowN : (2:ℝ)^k ≤ 2*N := by linarith [hb.2.1]
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log N ≤ k := by
    have hh := Real.log_le_log hN0 hNpow
    rw [Real.log_pow] at hh
    have hl2 : Real.log (2:ℝ) ≤ 1 := by
      have he := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      norm_num at he
      exact he
    have hm := mul_le_mul_of_nonneg_left hl2 hk0.le
    nlinarith only [hh,hm]
  have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  calc
    _ ≤ V ((2:ℝ)^k) := V_monotone hNpow
    _ ≤ dyadicTotientEnvelope J*(2:ℝ)^k/(k:ℝ) := dyadic_totient_count_le hk hkJ
    _ ≤ 2*dyadicTotientEnvelope J*N/(k:ℝ) := by
      apply div_le_div_of_nonneg_right _ hk0.le
      nlinarith only [mul_le_mul_of_nonneg_left hpowN hE]
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hlN hlog

lemma dyadic_value_count_one {J : ℕ} : V 1 ≤ dyadicTotientEnvelope J := by
  have hV : V 1 ≤ (1:ℝ) := V_le_self (by norm_num)
  exact hV.trans (dyadicTotientEnvelope_one_le J)

lemma log_floor_lower {x : ℝ} (hx : 4 ≤ x) :
    2 ≤ ⌊x⌋₊ ∧ Real.log x/2 ≤ Real.log (⌊x⌋₊:ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hN : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by norm_num; linarith)
  refine ⟨hN,?_⟩
  have hh : x/2 ≤ (⌊x⌋₊:ℝ) := by linarith [Nat.sub_one_lt_floor x]
  have hl := Real.log_le_log (by positivity : 0 < x/2) hh
  rw [Real.log_div (by linarith : x ≠ 0) (by norm_num)] at hl
  have hl4 : Real.log (4:ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have he : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [he] at hl4
  linarith

lemma V_floor (x : ℝ) : V (⌊x⌋₊:ℝ)=V x := by
  unfold V
  rw [Nat.floor_natCast]

lemma dyadic_real_value_count_bound {x : ℝ} {J : ℕ} (hx : 4 ≤ x)
    (hJ : x ≤ (2:ℝ)^J) : V x ≤ 4*dyadicTotientEnvelope J*x/Real.log x := by
  have hfloor := log_floor_lower hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hfloorlog : 0 < Real.log (⌊x⌋₊:ℝ) := lt_of_lt_of_le (by positivity) hfloor.2
  have hN : ⌊x⌋₊ ≤ 2^J := by
    exact_mod_cast (Nat.floor_le (by linarith : 0 ≤ x)).trans hJ
  have hb := dyadic_value_count_bound hfloor.1 hN
  rw [V_floor] at hb
  have hE : 0 ≤ dyadicTotientEnvelope J := zero_le_one.trans (dyadicTotientEnvelope_one_le J)
  calc
    _ ≤ 2*dyadicTotientEnvelope J*(⌊x⌋₊:ℝ)/Real.log (⌊x⌋₊:ℝ) := hb
    _ ≤ 2*dyadicTotientEnvelope J*x/Real.log (⌊x⌋₊:ℝ) := by
      apply div_le_div_of_nonneg_right _ hfloorlog.le
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) (by positivity)
    _ ≤ 2*dyadicTotientEnvelope J*x/(Real.log x/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfloor.2
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
