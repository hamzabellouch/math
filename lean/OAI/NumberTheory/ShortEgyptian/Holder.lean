import OAI.NumberTheory.ShortEgyptian.TerminalScale

namespace OAI

universe uι

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma finite_holder_card {ι : Type uι} (H : Finset ι) (f : ι → ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hf : ∀ i ∈ H, 0 ≤ f i) :
    ∑ i ∈ H, f i ≤ (H.card:ℝ)^(1-1/(r:ℝ))*(∑ i ∈ H, (f i)^r)^(1/(r:ℝ)) := by
  have hrR : 1 < (r:ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hc := Real.HolderConjugate.conjExponent hrR
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s:=H) (f:=f) (g:=fun _ => (1:ℝ)) hc hf (by intros; norm_num)
  rw [show 1/Real.conjExponent (r:ℝ) = 1-1/(r:ℝ) by simpa only [one_div] using hc.one_sub_inv.symm] at hh
  simpa only [mul_one,Real.one_rpow,sum_const, nsmul_eq_mul,Real.rpow_natCast,mul_comm] using hh

lemma holder_density {ι : Type uι} (H : Finset ι) (f : ι → ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hf : ∀ i ∈ H, 0 ≤ f i) (Y E : ℝ) (hY : 0 < Y)
    (hm : ∑ i ∈ H, (f i)^r ≤ Y*Real.exp E) :
    ∑ i ∈ H, f i ≤ Y*Real.exp (E/(r:ℝ))*((H.card:ℝ)/Y)^(1-1/(r:ℝ)) := by
  have hrp : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hh := (finite_holder_card H f r hr hf).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (sum_nonneg (fun i hi => pow_nonneg (hf i hi) r)) hm
      (by positivity : 0 ≤ 1/(r:ℝ))) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply hh.trans_eq
  rw [Real.mul_rpow hY.le (Real.exp_nonneg _),←Real.exp_mul,Real.div_rpow (Nat.cast_nonneg _) hY.le]
  have hy : Y^(1-1/(r:ℝ))*Y^(1/(r:ℝ)) = Y := by rw [←Real.rpow_add hY]; ring_nf; exact Real.rpow_one Y
  have hym : Y^(1-1/(r:ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hY _).ne'
  rw [show E*(1/(r:ℝ)) = E/(r:ℝ) by ring]
  rw [←mul_div_assoc]
  apply (eq_div_iff hym).mpr
  calc
    _ = (Y^(1-1/(r:ℝ))*Y^(1/(r:ℝ)))*Real.exp (E/(r:ℝ))*(H.card:ℝ)^(1-1/(r:ℝ)) := by ring
    _ = _ := by rw [hy]

end ShortEgyptian

end OAI
