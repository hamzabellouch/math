import Mathlib

namespace OAI

namespace SharpRamseyFive.PivotTree

noncomputable def potential (uA uB Q : ℝ) : ℝ := max 0 (Real.log (uA*uB/Q))

lemma cap_potential (u c n Q C : ℝ) (hn : 0<n) (hu : n≤u)
    (hc : 0<c) (hQ : 0<Q) (hC : 1≤C) (hcap : c≤C*Q/n) :
    potential c u Q ≤ Real.log (u/n)+Real.log C := by
  have hu0 : 0<u := hn.trans_le hu
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hd : 0≤Real.log (u/n) := Real.log_nonneg ((le_div_iff₀ hn).mpr (by simpa using hu))
  have hlC : 0≤Real.log C := Real.log_nonneg hC
  have hratio : c*u/Q≤C*(u/n) := by
    have hh := mul_le_mul_of_nonneg_right hcap hu0.le
    apply (div_le_iff₀ hQ).mpr
    convert hh using 1
    field_simp
  have hlog := Real.log_le_log (div_pos (mul_pos hc hu0) hQ) hratio
  rw [Real.log_mul hC0.ne' (div_pos hu0 hn).ne'] at hlog
  exact max_le (add_nonneg hd hlC) (by linarith)

theorem split_potential (uA uB nA nB cA cB Q C : ℝ)
    (hnA : 0<nA) (hnB : 0<nB) (hAu : nA≤uA) (hBu : nB≤uB)
    (hcA : 0<cA) (hcB : 0<cB) (hQ : 0<Q) (hC : 1≤C)
    (hAcap : cA≤C*Q/nB) (hBcap : cB≤C*Q/nA) :
    potential cA uB Q+potential uA cB Q ≤
      potential uA uB Q+Real.log (Q/(nA*nB))+2*Real.log C := by
  have h₁ := cap_potential uB cA nB Q C hnB hBu hcA hQ hC hAcap
  have h₂ := cap_potential uA cB nA Q C hnA hAu hcB hQ hC hBcap
  rw [potential,mul_comm cB uA] at h₂
  have huA : uA≠0 := (hnA.trans_le hAu).ne'
  have huB : uB≠0 := (hnB.trans_le hBu).ne'
  have hid : Real.log (uA/nA)+Real.log (uB/nB)=
      Real.log (uA*uB/Q)+Real.log (Q/(nA*nB)) := by
    rw [Real.log_div huA hnA.ne',Real.log_div huB hnB.ne',
      Real.log_div (mul_ne_zero huA huB) hQ.ne',
      Real.log_div hQ.ne' (mul_ne_zero hnA.ne' hnB.ne'),
      Real.log_mul huA huB,Real.log_mul hnA.ne' hnB.ne']
    ring
  have hG : Real.log (uA*uB/Q)≤potential uA uB Q := le_max_right _ _
  change potential cA uB Q+max 0 (Real.log (uA*cB/Q))≤_
  linarith

lemma log_deficits (uA uB nA nB Q : ℝ) (hnA : 0<nA) (hnB : 0<nB)
    (hAu : nA≤uA) (hBu : nB≤uB) (hQ : 0<Q) :
    Real.log (uA/nA)+Real.log (uB/nB) ≤
      potential uA uB Q+Real.log (Q/(nA*nB)) := by
  have huA : uA≠0 := (hnA.trans_le hAu).ne'
  have huB : uB≠0 := (hnB.trans_le hBu).ne'
  have he : Real.log (uA/nA)+Real.log (uB/nB)=
      Real.log (uA*uB/Q)+Real.log (Q/(nA*nB)) := by
    rw [Real.log_div huA hnA.ne',Real.log_div huB hnB.ne',
      Real.log_div (mul_ne_zero huA huB) hQ.ne',
      Real.log_div hQ.ne' (mul_ne_zero hnA.ne' hnB.ne'),
      Real.log_mul huA huB,Real.log_mul hnA.ne' hnB.ne']
    ring
  rw [he]
  have hh : Real.log (uA*uB/Q)≤potential uA uB Q := le_max_right _ _
  linarith

lemma initial_potential (q uA uB : ℝ) (hq : 1≤q) (hA : 0<uA) (hB : 0<uB)
    (hAu : uA≤2*q^4) (hBu : uB≤2*q^4) :
    potential uA uB (q^5)≤3*Real.log q+Real.log 4 := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hprod := mul_le_mul hAu hBu hB.le (by positivity : (0:ℝ)≤2*q^4)
  have hratio : uA*uB/q^5 ≤ 4*q^3 := by
    apply (div_le_iff₀ (pow_pos hq0 _)).mpr
    nlinarith only [hprod]
  have hl := Real.log_le_log (by positivity : 0<uA*uB/q^5) hratio
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (pow_ne_zero _ hq0.ne'),Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  exact max_le (by positivity [Real.log_nonneg hq,Real.log_nonneg (by norm_num : (1:ℝ)≤4)])
    (by linarith)

end SharpRamseyFive.PivotTree

end OAI
