import Mathlib

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation

lemma collar_error_budget (κ η shells closed : ℝ) (hκ : 0<κ) (hκ1 : κ≤1)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hclosed : 0<closed) (hshells : 4/(κ*closed)<shells) :
    1/(shells*closed)+Real.exp (-Real.log (4/κ))+
      (Real.log (4/κ)+1)*η/(κ/4)+κ/4 ≤ κ := by
  have hratio : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  have hK : 0 ≤ Real.log (4/κ) := Real.log_nonneg hratio
  have hK1 : 0<Real.log (4/κ)+1 := by linarith
  have hlam : 0<κ/4 := by linarith
  have hden : 0<κ*closed := mul_pos hκ hclosed
  have hs : 0<shells := (div_pos (by norm_num) hden).trans hshells
  have hfirst : 1/(shells*closed) ≤ κ/4 := by
    apply (div_le_iff₀ (mul_pos hs hclosed)).mpr
    have hh := (div_lt_iff₀ hden).mp hshells
    nlinarith
  have hexp : Real.exp (-Real.log (4/κ))=κ/4 := by
    rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) hκ)]
    simp
  have hthird : (Real.log (4/κ)+1)*η/(κ/4) ≤ κ/4 := by
    apply (div_le_iff₀ hlam).mpr
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hK1)).mp hη
    nlinarith
  rw [hexp]
  linarith

lemma positive_trial_power (p : ℝ) (hp : 0<p) (m VM : ℕ) :
    0<(p/2)^(m+1+VM) := pow_pos (by linarith) _

lemma trial_ceiling_budget (K s : ℝ) (hs : 0<s) :
    K ≤ (⌈K/s⌉₊ : ℝ)*s := by
  have hh : K/s ≤ (⌈K/s⌉₊ : ℝ) := Nat.le_ceil _
  exact (div_le_iff₀ hs).mp hh

end CriticalPercolation
end
end
end

end OAI
