import Mathlib

namespace OAI

namespace MetricKMedianRecovery.Sensitivity
lemma power_bound (L : ℕ) (hL : 0 < L) (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    (1+xi/(4*L))^(2*L) < 1+xi := by
  have hLR : (0:ℝ) < L := by exact_mod_cast hL
  have hb : 0 < xi/(4*L) := by positivity
  have hlog := Real.log_lt_sub_one_of_pos (by positivity : 0 < 1+xi/(4*L))
      (by linarith : 1+xi/(4*(L:ℝ)) ≠ 1)
  have hlow := Real.le_log_one_add_of_nonneg hxi.le
  have hfrac : xi/2 ≤ 2*xi/(xi+2) := by
    apply (le_div_iff₀ (by linarith : 0 < xi+2)).mpr
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hlog (by positivity : 0 < (2*L:ℝ))
  have hbeta : (2*L:ℝ)*(xi/(4*L)) = xi/2 := by field_simp; ring
  have hc : Real.log ((1+xi/(4*L))^(2*L)) < Real.log (1+xi) := by
    rw [Real.log_pow]
    push_cast
    rw [show 1+xi/(4*(L:ℝ))-1 = xi/(4*L) by ring,hbeta] at hmul
    exact hmul.trans_le (hfrac.trans hlow)
  exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hc

lemma chain_bound_length (P : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) (a d : ℕ)
    (hstep : ∀ j, a < j → j ≤ a+d → P (j-1) ≤ q*P j) :
    P a ≤ q^d*P (a+d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hi : P a ≤ q^d*P (a+d) := ih (fun j hj hjd => hstep j hj (by omega))
    have hs := hstep (a+d+1) (by omega) (by omega)
    have he : a+d+1-1=a+d := by omega
    rw [he] at hs
    have hs' : P (a+d) ≤ q*P (a+(d+1)) := by simpa only [Nat.add_assoc] using hs
    calc
      _ ≤ q^d*P (a+d) := hi
      _ ≤ q^d*(q*P (a+(d+1))) := mul_le_mul_of_nonneg_left hs' (pow_nonneg hq _)
      _ = _ := by rw [pow_succ]; ring

lemma chain_bound (P : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) (a b : ℕ) (hab : a ≤ b)
    (hstep : ∀ j, a < j → j ≤ b → P (j-1) ≤ q*P j) :
    P a ≤ q^(b-a)*P b := by
  have he : a+(b-a)=b := Nat.add_sub_of_le hab
  simpa only [he] using chain_bound_length P q hq a (b-a)
    (fun j hj hjb => hstep j hj (by simpa only [he] using hjb))

theorem exists_sensitive (P : ℕ → ℝ) (k L : ℕ) (hL : 0 < L) (hk : 2*L < k)
    (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hPk : 0 ≤ P k)
    (hsens : (1+xi)*P k < P (k-2*L)) :
    ∃ h : ℕ, k-2*L < h ∧ h ≤ k ∧
      (1+xi/(4*L))*P h ≤ P (h-1) ∧ P h ≤ (1+xi)*P k := by
  classical
  let q := 1+xi/(4*L)
  have hq1 : 1 ≤ q := by
    have hb : 0 ≤ xi/(4*(L:ℝ)) := div_nonneg hxi.le (by positivity)
    dsimp [q]; linarith
  have hq : 0 ≤ q := le_trans (by norm_num) hq1
  let A := (Finset.Ioc (k-2*L) k).filter (fun j => q*P j ≤ P (j-1))
  have hA : A.Nonempty := by
    by_contra hn
    have hstep (j : ℕ) (hja : k-2*L < j) (hjk : j ≤ k) : P (j-1) ≤ q*P j := by
      by_contra hh
      apply hn
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hja,hjk⟩,(lt_of_not_ge hh).le⟩⟩
    have hh := chain_bound P q hq (k-2*L) k (by omega) hstep
    have hex : k-(k-2*L)=2*L := by omega
    rw [hex] at hh
    have hp := mul_le_mul_of_nonneg_right (power_bound L hL xi hxi hxi1).le hPk
    exact (not_lt_of_ge (hh.trans hp)) hsens
  let h := A.max' hA
  have hm : h ∈ A := Finset.max'_mem A hA
  have hmem := Finset.mem_filter.mp hm
  have hr := Finset.mem_Ioc.mp hmem.1
  have hstep (j : ℕ) (hhj : h < j) (hjk : j ≤ k) : P (j-1) ≤ q*P j := by
    by_contra hn
    have hjA : j ∈ A := Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨lt_trans hr.1 hhj,hjk⟩,(lt_of_not_ge hn).le⟩
    have hmax : j ≤ h := Finset.le_max' A j hjA
    omega
  have hc := chain_bound P q hq h k hr.2 hstep
  have hex : k-h ≤ 2*L := by omega
  have hpow : q^(k-h) ≤ q^(2*L) := pow_le_pow_right₀ hq1 hex
  have hp : q^(k-h) ≤ 1+xi := hpow.trans (power_bound L hL xi hxi hxi1).le
  exact ⟨h,hr.1,hr.2,hmem.2,hc.trans (mul_le_mul_of_nonneg_right hp hPk)⟩

end MetricKMedianRecovery.Sensitivity

end OAI
