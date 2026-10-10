import Mathlib

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter
open scoped Topology
noncomputable section

theorem finite_affine_recurrence (a b d : ℝ) (D : ℕ→ℝ)
    (hb : 0≤b) (hb' : b<1) (hD : D 0≤d)
    (hstep : ∀n,D (n+1)≤a+b*D n) :
    ∀n,D n≤a/(1-b)*(1-b^n)+b^n*d := by
  intro n
  induction n with
  | zero => simpa using hD
  | succ n ih =>
    apply (hstep n).trans
    have hineq:=mul_le_mul_of_nonneg_left ih hb
    have hnz : 1-b≠0 := ne_of_gt (sub_pos.mpr hb')
    calc
      a+b*D n≤a+b*(a/(1-b)*(1-b^n)+b^n*d) := add_le_add le_rfl hineq
      _ = a/(1-b)*(1-b^(n+1))+b^(n+1)*d := by rw [pow_succ]; field_simp; ring

theorem compression_recurrence_terminal (σ η β : ℝ) (m : ℕ) (D : ℕ→ℝ)
    (hσ : 1≤σ) (_hη : 0<η) (_hβ : 0≤β)
    (ha : 2≤σ^(2*β)) (hr : σ^(-η/4)≤(1:ℝ)/3)
    (hm : 1≤η*(m:ℝ)/4) (hD : D 0≤σ)
    (hstep : ∀n,D (n+1)≤σ^(2*β)+D n*σ^(-η/4)) :
    D m≤2*σ^(2*β) := by
  have hs : 0<σ := lt_of_lt_of_le zero_lt_one hσ
  have hp : 0≤σ^(-η/4) := Real.rpow_nonneg hs.le _
  have hb : σ^(-η/4)<1 := lt_of_le_of_lt hr (by norm_num)
  have hh:=finite_affine_recurrence (σ^(2*β)) (σ^(-η/4)) σ D hp hb hD
    (fun n=>by simpa only [mul_comm] using hstep n) m
  have hnon : 0≤σ^(2*β) := Real.rpow_nonneg hs.le _
  have hden : (2:ℝ)/3≤1-σ^(-η/4) := by linarith
  have hfac : σ^(2*β)/(1-σ^(-η/4))≤(3/2)*σ^(2*β) := by
    have h:=div_le_div_of_nonneg_left hnon (by norm_num : (0:ℝ)<2/3) hden
    calc
      _ ≤ σ^(2*β)/(2/3) := h
      _ = _ := by ring
  have htail : (σ^(-η/4))^m*σ≤1 := by
    calc
      _ = σ^((-η/4)*(m:ℝ)+1) := by
        rw [Real.rpow_add hs,Real.rpow_one,Real.rpow_mul hs.le,Real.rpow_natCast]
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hσ (by nlinarith)
  have hpow0 : 0≤(σ^(-η/4))^m := pow_nonneg hp _
  have hquot0 : 0≤σ^(2*β)/(1-σ^(-η/4)) := div_nonneg hnon (sub_nonneg.mpr hb.le)
  have hprod : σ^(2*β)/(1-σ^(-η/4))*(1-(σ^(-η/4))^m)≤(3/2)*σ^(2*β) := by
    apply le_trans _ hfac
    nlinarith
  linarith
end
end SharpRamseyFive.ParameterHierarchy

end OAI
