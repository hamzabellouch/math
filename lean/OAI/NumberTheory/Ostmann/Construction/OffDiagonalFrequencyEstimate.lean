import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsEquation48

namespace OAI

open Erdos970

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Ostmann.Construction
open Arithmetic.HistoryProductWindows Conclusion

theorem reversal_frequency_exp_bound (s v w : ℤ) (Hp Hm U p G T Δ E WH Wu : ℝ)
    (hHp : 0 < Hp) (hHm : 0 < Hm) (hU : 0 < U) (hp : 0 < p)
    (hv : |(v:ℝ)| ≤ Real.exp E) (hw : |(w:ℝ)| ≤ Real.exp E)
    (hlogHp : Real.log Hp ≤ G+T+Δ+WH) (hlogHm : Real.log Hm ≤ G+T+Δ+WH)
    (hlogU : T-Wu ≤ Real.log U) (hlogp : G-1 ≤ Real.log p)
    (heq : (s:ℝ)*U*p = (v:ℝ)*Hm-(w:ℝ)*Hp) :
    |(s:ℝ)| ≤ Real.exp (E+Δ+WH+Wu+1+Real.log 2) := by
  have hHp' := (Real.log_le_iff_le_exp hHp).mp hlogHp
  have hHm' := (Real.log_le_iff_le_exp hHm).mp hlogHm
  have hU' := (Real.le_log_iff_exp_le hU).mp hlogU
  have hp' := (Real.le_log_iff_exp_le hp).mp hlogp
  have hnum : |(v:ℝ)*Hm-(w:ℝ)*Hp| ≤
      2*(Real.exp E*Real.exp (G+T+Δ+WH)) := by
    have he := abs_sub ((v:ℝ)*Hm) ((w:ℝ)*Hp)
    rw [abs_mul,abs_mul,abs_of_pos hHm,abs_of_pos hHp] at he
    have hv' := mul_le_mul hv hHm' hHm.le (Real.exp_pos E).le
    have hw' := mul_le_mul hw hHp' hHp.le (Real.exp_pos E).le
    linarith
  have hden : Real.exp (T-Wu)*Real.exp (G-1) ≤ U*p :=
    mul_le_mul hU' hp' (Real.exp_pos _).le hU.le
  have hform : |(s:ℝ)| = |(v:ℝ)*Hm-(w:ℝ)*Hp|/(U*p) := by
    rw [←heq,abs_mul,abs_mul,abs_of_pos hU,abs_of_pos hp]
    field_simp
  rw [hform]
  calc
    _ ≤ (2*(Real.exp E*Real.exp (G+T+Δ+WH)))/
        (Real.exp (T-Wu)*Real.exp (G-1)) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = _ := by
      rw [←Real.exp_add,←Real.exp_add,mul_div_assoc,←Real.exp_sub]
      have he : E+(G+T+Δ+WH)-((T-Wu)+(G-1)) = E+Δ+WH+Wu+1 := by ring
      rw [he,Real.exp_add (E+Δ+WH+Wu+1) (Real.log 2),
        Real.exp_log (by norm_num : (0:ℝ)<2)]
      ring

theorem frequencyBudget_succ (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) :
    frequencyBudget Bs BD Bz k L (l+1) = frequencyBudget Bs BD Bz k L l+
      stepGap BD Bz k L l+(2:ℝ)^l*Real.sqrt (bulkSize k L) := by
  simp only [frequencyBudget,Finset.sum_range_succ,pow_succ]
  ring

theorem frequency_window_reserve_of_sqrt (k : ℕ) (Bs BD Bz L : ℝ)
    (hL : 20+10*(k:ℝ)+Real.log 2 ≤ Real.sqrt (bulkSize k L)) (l : ℕ) :
      frequencyBudget Bs BD Bz k L l+stepGap BD Bz k L l+
        nominalInheritedWidth k l+nominalRemovedWidth k l+1+Real.log 2 ≤
          frequencyBudget Bs BD Bz k L (l+1) := by
  rw [frequencyBudget_succ]
  have hr : (1:ℝ) ≤ (2:ℝ)^l := one_le_pow₀ (by norm_num)
  have hc : 0 ≤ 2+Real.log 2 := by positivity
  have he := mul_le_mul_of_nonneg_left hL (show 0 ≤ (2:ℝ)^l by positivity)
  have hsmall := mul_le_mul_of_nonneg_right hr hc
  unfold nominalInheritedWidth nominalRemovedWidth
  nlinarith

theorem frequency_window_reserve {k : ℕ} (hk : 0<k) (Bs BD Bz : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀l : ℕ,
      frequencyBudget Bs BD Bz k L l+stepGap BD Bz k L l+
        nominalInheritedWidth k l+nominalRemovedWidth k l+1+Real.log 2 ≤
          frequencyBudget Bs BD Bz k L (l+1) := by
  have hs := (Real.tendsto_sqrt_atTop.comp (bulkSize_tendsto_atTop hk)).eventually
    (eventually_ge_atTop (20+10*(k:ℝ)+Real.log 2))
  filter_upwards [hs] with L hL l
  exact frequency_window_reserve_of_sqrt k Bs BD Bz L hL l

theorem int_le_exp_of_natAbs_le_frequencyBound (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (l : ℕ) (v : ℤ) (hv : v.natAbs ≤ frequencyBound Bs BD Bz k L l) :
    |(v:ℝ)| ≤ Real.exp (frequencyBudget Bs BD Bz k L l) := by
  have hf := Nat.floor_le (Real.exp_pos (frequencyBudget Bs BD Bz k L l)).le
  have hv' : (v.natAbs:ℝ) ≤ (frequencyBound Bs BD Bz k L l:ℝ) := by exact_mod_cast hv
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hv'.trans hf

theorem int_natAbs_le_frequencyBound_of_exp (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (l : ℕ) (v : ℤ) (hv : |(v:ℝ)| ≤ Real.exp (frequencyBudget Bs BD Bz k L l)) :
    v.natAbs ≤ frequencyBound Bs BD Bz k L l := by
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hv

end Ostmann.Construction

end

end OAI
