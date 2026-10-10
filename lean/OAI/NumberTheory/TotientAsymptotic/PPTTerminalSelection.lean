import OAI.NumberTheory.TotientAsymptotic.PPTTerminalGap
import OAI.NumberTheory.TotientAsymptotic.PPTGridSeparation

namespace OAI

/-! A finite terminal-window label with enough room for alignment and grid errors. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

/-- The terminal cutoff is selected from `N+1` explicit windows. The
entire normality and paired-grid budget fits inside a quarter of the
chosen vacant interval. -/
theorem ppt_select_terminal_window {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (N H : ℕ) (x : Fin N → ℝ) (s : ℝ),
      ∀ hN : 0 < N,
      Antitone x → N ≤ H → 1 ≤ H → (H : ℝ) ≤ A*Real.log t →
      0 ≤ s → s ≤ (H : ℝ)^4 → 2*t^(2/3 : ℝ) < x ⟨0,hN⟩ →
      ∃ j : Fin (N+1), ∃ J : ℕ,
        let L := t^(2/3 : ℝ)+2*(j.val : ℝ)*(t^(2/3 : ℝ)/(2*((N : ℝ)+1)))
        let U := t^(2/3 : ℝ)+(2*(j.val : ℝ)+1)*(t^(2/3 : ℝ)/(2*((N : ℝ)+1)))
        t^(2/3 : ℝ) ≤ L ∧ U ≤ 2*t^(2/3 : ℝ) ∧
        0 < J ∧ J ≤ N ∧
        (∀ i : Fin N, i.val < J → U < x i) ∧
        (∀ i : Fin N, J ≤ i.val → x i < L) ∧
        (2*(H : ℝ)+1)*Real.sqrt (s*t)+s+
          (8*(H : ℝ)+20)*(2*((Real.log t)^5/Real.sqrt t))*t < (U-L)/4 := by
  filter_upwards [ppt_terminal_normality_budget hA (by norm_num : (0 : ℝ) < 1/16),
    ppt_log_dimension_separation hA, eventually_gt_atTop (0 : ℝ)]
    with t hnormal hgrid ht
  intro N H x s hN hx hNH hH hdim hs0 hs hhead
  let T : ℝ := t^(2/3 : ℝ)
  let δ : ℝ := T/(2*((N : ℝ)+1))
  have hT : 0 < T := Real.rpow_pos_of_pos ht _
  have hdenN : 0 < 2*((N : ℝ)+1) := by positivity
  have hδ : 0 < δ := div_pos hT hdenN
  obtain ⟨j, hj⟩ := ppt_empty_separated_window (T := T) x hδ
  let L : ℝ := T+2*(j.val : ℝ)*δ
  let U : ℝ := T+(2*(j.val : ℝ)+1)*δ
  obtain ⟨J, hJN, hhigh, hlow⟩ := ppt_antitone_split_at_empty_window x hx hj
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hjN : (j.val : ℝ) ≤ N := by
    exact_mod_cast (Nat.lt_succ_iff.mp j.isLt)
  have hδscale : (2*((N : ℝ)+1))*δ = T := by dsimp only [δ]; field_simp
  have hL : T ≤ L := by
    have hh : 0 ≤ 2*(j.val : ℝ)*δ := by positivity
    dsimp only [L]
    linarith only [hh]
  have hU : U ≤ 2*T := by dsimp only [U]; nlinarith only [hδscale, hjN, hδ]
  have hwidth : U-L = δ := by dsimp only [U, L]; ring
  have hJ : 0 < J := by
    by_contra hh
    have hJ0 : J = 0 := Nat.eq_zero_of_not_pos hh
    have hl := hlow ⟨0,hN⟩ (by omega)
    have hLU : L < U := by rw [← sub_pos, hwidth]; exact hδ
    change 2*T < x ⟨0,hN⟩ at hhead
    linarith only [hl, hLU, hU, hhead]
  have hwide : T/(2*((H : ℝ)+1)) ≤ U-L := by
    rw [hwidth]
    exact div_le_div_of_nonneg_left hT.le hdenN
      (by exact_mod_cast (show 2*(N+1) ≤ 2*(H+1) by omega))
  have hnormal' : (2*(H : ℝ)+1)*Real.sqrt (s*t)+s < T/(16*((H : ℝ)+1)) := by
    have hh := hnormal H H s t hH le_rfl hdim hs0 hs ht.le le_rfl
    convert hh using 1
    dsimp only [T]
    field_simp
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHr
  have hH3 : (H : ℝ) ≤ (H : ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hHr (show 1 ≤ 3 by omega)
  have hden : 16*((H : ℝ)+1) ≤ 40*(H : ℝ)^3 := by nlinarith only [hHr, hH3]
  have hgrid' :
      (8*(H : ℝ)+20)*(2*((Real.log t)^5/Real.sqrt t))*t < T/(16*((H : ℝ)+1)) := by
    have hg0 : (8*(H : ℝ)+20)*(2*((Real.log t)^5/Real.sqrt t)) <
        1/(40*(H : ℝ)^3*t^(1/3 : ℝ)) := by
      simpa only [mul_div_assoc] using hgrid H hH hdim
    have hg := mul_lt_mul_of_pos_right hg0 ht
    have hprod : t^(1/3 : ℝ)*T = t := by
      dsimp only [T]
      rw [← Real.rpow_add ht]
      norm_num
    have hquot : (1/(40*(H : ℝ)^3*t^(1/3 : ℝ)))*t = T/(40*(H : ℝ)^3) := by
      have ht13 : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht _
      calc
        _ = (1/(40*(H : ℝ)^3*t^(1/3 : ℝ)))*(t^(1/3 : ℝ)*T) := by rw [hprod]
        _ = _ := by field_simp
    rw [hquot] at hg
    exact hg.trans_le (div_le_div_of_nonneg_left hT.le (by positivity) hden)
  refine ⟨j, J, hL, hU, hJ, hJN, hhigh, hlow, ?_⟩
  have hw : 8*(T/(16*((H : ℝ)+1))) ≤ U-L := by
    convert hwide using 1
    field_simp
    norm_num
  linarith only [hnormal', hgrid', hw]

end TotientAsymptotic

end

end OAI
