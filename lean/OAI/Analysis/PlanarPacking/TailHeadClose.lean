import OAI.Analysis.PlanarPacking.TailHeadBounds

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma headRational_expand (p : CardinalData) (s : ℝ) :
    headRational p s=p.C+(p.c₀/s^2+p.d₀/s)+
      ∑ i : Fin 21,(p.x (shortNode i,false)/(s-(shortNode i).val)^2+
        p.x (shortNode i,true)/(s-(shortNode i).val)) := by
  simp only [headRational,Fintype.sum_option,headC,headD,headNodeNat,Nat.cast_zero,sub_zero]
  ring
lemma headRational_sub (p q : CardinalData) (hC : p.C=q.C) (hc : p.c₀=q.c₀)
    (hd : p.d₀=q.d₀) (s : ℝ) :
    headRational p s-headRational q s=
      ∑ i : Fin 21,((p.x-q.x) (shortNode i,false)/(s-(shortNode i).val)^2+
        (p.x-q.x) (shortNode i,true)/(s-(shortNode i).val)) := by
  rw [headRational_expand,headRational_expand,hC,hc,hd]
  simp only [lp.coeFn_sub,Pi.sub_apply,sub_div,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring
lemma reciprocal_pair_abs {u v t : ℝ} (ht : (3:ℝ)/2 ≤ t) :
    |u/t^2+v/t| ≤ (|u|+|v|)*(2/3) := by
  have hp : 0<t := by linarith
  have ht2 : (3:ℝ)/2 ≤ t^2 := by nlinarith
  have hu:=div_le_div_of_nonneg_left (abs_nonneg u) (by norm_num : (0:ℝ)<3/2) ht2
  have hv:=div_le_div_of_nonneg_left (abs_nonneg v) (by norm_num : (0:ℝ)<3/2) ht
  have hh:=abs_add_le (u/t^2) (v/t)
  rw [abs_div,abs_div,abs_pow,abs_of_pos hp] at hh
  nlinarith
lemma short_norm_bound (x : X) :
    (∑ i : Fin 21,(|x (shortNode i,false)|+|x (shortNode i,true)|)) ≤ ‖x‖ := by
  rw [X_norm]
  simpa only [tsum_fintype,Function.comp_apply] using
    tsum_comp_le_tsum_of_inj (X_summable_pairs x) (fun n => add_nonneg (abs_nonneg _) (abs_nonneg _)) shortNode_inj
lemma head_difference_bound (p q : CardinalData) (hC : p.C=q.C) (hc : p.c₀=q.c₀)
    (hd : p.d₀=q.d₀) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    |headRational p s-headRational q s| ≤ ‖p.x-q.x‖*(2/3) := by
  rw [headRational_sub p q hC hc hd]
  calc
    _ ≤ ∑ i : Fin 21, |(p.x-q.x) (shortNode i,false)/(s-(shortNode i).val)^2+
        (p.x-q.x) (shortNode i,true)/(s-(shortNode i).val)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 21,(|(p.x-q.x) (shortNode i,false)|+|(p.x-q.x) (shortNode i,true)|)*(2/3) := by
      apply Finset.sum_le_sum; intro i hi
      apply reciprocal_pair_abs
      have hn : ((shortNode i).val:ℝ) ≤ 40 := by exact_mod_cast shortNode_le i
      linarith
    _ ≤ ‖p.x-q.x‖*(2/3) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (short_norm_bound _) (by norm_num)
lemma exact_head_difference (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    |headRational (tableData a) s-headRational (exactData a) s| < (2:ℝ)/10^5 := by
  have hfix:=table_exact_fixed a
  have hh:=head_difference_bound (tableData a) (exactData a) hfix.1 hfix.2.1 hfix.2.2 hs
  rw [exactData_x] at hh
  change |headRational (tableData a) s-headRational (exactData a) s| ≤ ‖coefficientError a‖*(2/3) at hh
  linarith [coefficient_error_bound a]
lemma exact_head_lower (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    (11:ℝ)/1000<(if a then 1 else -1)*headRational (exactData a) s := by
  have hh:=table_head_lower a hs
  have he:=abs_lt.mp (exact_head_difference a hs)
  cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hh ⊢ <;> linarith
end SharpPlanar

end OAI
