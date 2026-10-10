import Mathlib

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section

lemma window_diff_sum (e l : ℕ→ℝ) (w : ℕ) (c hi : ℝ)
    (he : e 0≤hi) (hn : ∀ j< w,e (j+1)≤l j+c) :
    (∑ j∈Finset.range (w+1),(e j-l j))≤hi-l w+(w:ℝ)*c := by
  induction w with
  | zero => simp only [Nat.zero_add,Finset.sum_range_one,Nat.cast_zero,zero_mul,add_zero]; linarith
  | succ w ih =>
    have hh:=ih (fun j hj=>hn j (by omega))
    have ha:=hn w (by omega)
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    linarith

theorem window_drop_sum (e l : ℕ→ℝ) (w : ℕ) (lo hi c : ℝ)
    (hc : 0≤c) (hlo : lo≤hi) (he : e 0≤hi)
    (hl : ∀ j<w,lo≤l j) (hw : ∀ j<w,l j≤e j+c)
    (hn : ∀ j,j+1<w→e (j+1)≤l j+c) :
    (∑ j∈Finset.range w,max 0 (e j-l j))≤hi-lo+2*(w:ℝ)*c := by
  cases w with
  | zero => simpa using sub_nonneg.mpr hlo
  | succ v =>
    have hd:=window_diff_sum e l v c hi he (fun j hj=>hn j (by omega))
    have hh : (∑ j∈Finset.range (v+1),max 0 (e j-l j))≤
        (∑ j∈Finset.range (v+1),(e j-l j))+(v+1:ℕ)*c := by
      calc
        _ ≤ ∑ j∈Finset.range (v+1),((e j-l j)+c) := by
          apply Finset.sum_le_sum
          intro j hj
          have h:=hw j (Finset.mem_range.mp hj)
          exact max_le (by linarith) (by linarith)
        _ = _ := by simp [Finset.sum_add_distrib]
    have hb:=hl v (by omega)
    norm_num only [Nat.cast_add,Nat.cast_one] at *
    have hv : 0≤(v:ℝ)*c := mul_nonneg (Nat.cast_nonneg _) hc
    linarith

theorem large_window_count (e l : ℕ→ℝ) (w : ℕ) (lo hi c k : ℝ)
    (hc : 0≤c) (hk : 0<k) (hlo : lo≤hi) (he : e 0≤hi)
    (hl : ∀ j<w,lo≤l j) (hw : ∀ j<w,l j≤e j+c)
    (hn : ∀ j,j+1<w→e (j+1)≤l j+c) :
    (((Finset.range w).filter fun j=>k<e j-l j).card:ℝ)≤
      (hi-lo+2*(w:ℝ)*c)/k := by
  apply (le_div_iff₀ hk).mpr
  calc
    _ = ∑ j∈(Finset.range w).filter (fun j=>k<e j-l j),k := by simp
    _ ≤ ∑ j∈(Finset.range w).filter (fun j=>k<e j-l j),max 0 (e j-l j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ((Finset.mem_filter.mp hj).2.le).trans (le_max_right _ _)
    _ ≤ ∑ j∈Finset.range w,max 0 (e j-l j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
    _ ≤ _ := window_drop_sum e l w lo hi c hc hlo he hl hw hn

theorem pivot_support_product (q u v k d a b : ℝ) (hq : 0<q)
    (hdrop : u-v≤d)
    (ha : Real.exp (5*Real.log q-u-k)/2≤a)
    (hb : Real.exp (v-k)/2≤b) :
    q^5*Real.exp (-d-2*k)/4≤a*b := by
  have he : Real.exp (5*Real.log q-u-k)/2*(Real.exp (v-k)/2)=
      q^5*Real.exp (v-u-2*k)/4 := by
    rw [div_mul_div_comm,←Real.exp_add]
    have hx : (5*Real.log q-u-k)+(v-k)=5*Real.log q+(v-u-2*k) := by ring
    have hfive : Real.exp (5*Real.log q)=Real.exp (Real.log q)^5 := by
      simpa using Real.exp_nat_mul (Real.log q) 5
    rw [hx,Real.exp_add,hfive,Real.exp_log hq]
    norm_num
  have hle := mul_le_mul ha hb (by positivity : 0≤Real.exp (v-k)/2)
    ((by positivity : 0≤Real.exp (5*Real.log q-u-k)/2).trans ha)
  rw [he] at hle
  refine le_trans ?_ hle
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
end
end SharpRamseyFive.FiniteEntropy

end OAI
