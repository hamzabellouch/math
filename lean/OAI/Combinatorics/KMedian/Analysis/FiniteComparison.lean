import Mathlib
import OAI.Combinatorics.KMedian.Analysis.RowComparison
import OAI.Combinatorics.KMedian.Analysis.QuadraticEnvelopes
import OAI.Combinatorics.KMedian.Analysis.ComparisonCertificates
import OAI.Combinatorics.KMedian.Analysis.NormalizedTransfer

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

open Analytic

noncomputable def actualB (x w : ℝ) (s : Bool) : ℝ :=
  (2-ScalarTransfer.bit s)*P x*(x+w)

private theorem scalarC (p : ℝ) (s : Bool) : ScalarTransfer.c p s = C p s := by
  cases s <;> simp [ScalarTransfer.c, ScalarTransfer.bit, C]
private theorem scalarD (s : Bool) : ScalarTransfer.d s = d s := rfl
private theorem actualB_nonneg {x w : ℝ} (hx : 0 ≤ x) (hw : 0 ≤ w) (s : Bool) :
    0 ≤ actualB x w s := by
  have hp := P_nonneg x
  cases s <;> norm_num [actualB, ScalarTransfer.bit] <;> positivity

private theorem proxy_N {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    ScalarTransfer.N (P x) (Certificates.k (1-x)) s ≤ C (P x) s-k (P x) s := by
  have hk := Certificates.k_envelope hx0 hx
  cases s <;> norm_num [ScalarTransfer.N, ScalarTransfer.c, ScalarTransfer.bit, C, k]; linarith

private theorem actual_first {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (s : Bool) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1) :
    m x+actualB x w s-(2/5)*(P x*w^2)/r ≤ C (P x) s*(1-P x)/(1-P x*r) := by
  have hm : (1+x)*(m x+2*x*P x)=2*x*(1-P x) := by
    simpa only [m, sub_add_cancel] using coefficient_identity x
  have h := ScalarTransfer.first_scalar (P_nonneg x) (P_le_half hx0) hx0 hx hw0 hw hr0 hr
    hm (Certificates.T1_actual_pos hx0 hx).le (Certificates.T2_actual_pos hx0 hx).le s
  simpa only [actualB, scalarC] using h

private theorem actual_L {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (s : Bool) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) :
    0 ≤ L (P x) (m x) (P x*w^2) (actualB x w) s r := by
  rcases eq_or_lt_of_le hr0 with hzero | hpos
  · rw [←hzero]; unfold L; simp only [mul_zero, zero_add]; have hp := P_nonneg x; positivity
  · have hf := actual_first hx0 hx hw0 hw s hpos hr
    have hp0 := P_nonneg x
    have hp := P_le_half hx0
    have hd := denominator_pos hp hp0 hr
    have hpr : P x*r ≤ P x := mul_le_of_le_one_right hp0 hr
    have hfrac : C (P x) s*(1-P x)/(1-P x*r) ≤ C (P x) s := by
      apply (div_le_iff₀ hd).mpr
      exact mul_le_mul_of_nonneg_left (by linarith) (C_pos hp s).le
    have hdiv : m x+actualB x w s-C (P x) s ≤ (2/5)*(P x*w^2)/r := by linarith
    have hmul := (le_div_iff₀ hpos).mp hdiv
    unfold L
    nlinarith only [hmul]

private theorem actual_linear {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (_hw0 : 0 ≤ w) (hw : w ≤ 1-x) (s : Bool) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) :
    d s*G (P x) (m x) (A x+2*P x*w) (P x*w^2) (actualB x w) s r ≤
      K (P x) (P x*w^2) (actualB x w) s r := by
  have hl := ScalarTransfer.linear_scalar (P_nonneg x) hw hr0 hr s
    (Certificates.Q0_actual_pos hx0 hx s).le (Certificates.Q1_actual_pos hx0 hx s).le
  have hm : ScalarTransfer.stdM (P x) (A x) w r s = M (P x) (A x+2*P x*w) s r := by
    simp only [ScalarTransfer.stdM, scalarC, M]
  have hL : ScalarTransfer.stdL (P x) (A x) x w r s =
      L (P x) (m x) (P x*w^2) (actualB x w) s r := by
    simp only [ScalarTransfer.stdL, scalarC, ScalarTransfer.stdB, L, m, actualB, mul_assoc]
  have hk : ScalarTransfer.stdK (P x) (Certificates.k (1-x)) x w r s ≤
      K (P x) (P x*w^2) (actualB x w) s r := by
    have hn := proxy_N hx0 hx s
    unfold ScalarTransfer.stdK ScalarTransfer.stdB K actualB
    linarith only [hn]
  rw [hm, hL, scalarD] at hl
  exact hl.trans hk

private theorem actual_P_small {x : ℝ} (_hx0 : 0 ≤ x) (_hx : x ≤ 1) (hside : 1-x ≤ 1/2) :
    P x ≤ 47/100 := by
  have hanti := P_antitone (show (1/2:ℝ) ≤ x by linarith)
  have happ := (abs_le.mp (Certificates.p_approximation (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1))).1
  norm_num [Certificates.p] at happ
  linarith

private theorem kappa_absorb {p b q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 47/100)
    (hb : p ≤ b) (_hq0 : 0 ≤ q) (hq : q ≤ 1) :
    (13/25)*(psi p q-(1-q)) ≤ b*(1-q) := by
  have hph : p ≤ 1/2 := by linarith
  have hd := denominator_pos hph hp0 hq
  have hid : psi p q-(1-q)=p*q*(1-q)/(1-p*q) := by
    apply (eq_div_iff hd.ne').mpr
    unfold psi
    rw [sub_mul, div_mul_cancel₀ _ hd.ne']
    ring
  have hpq := mul_le_of_le_one_right hp0 hq
  have hh : (13/25)*q ≤ 1-p*q := by linarith
  have hmul := mul_le_mul_of_nonneg_left hh hp0
  have hmul' := mul_le_mul_of_nonneg_right hb hd.le
  have hn := mul_le_mul_of_nonneg_right (hmul.trans hmul') (sub_nonneg.mpr hq)
  rw [hid]
  rw [←mul_div_assoc, div_le_iff₀ hd]
  nlinarith only [hn]

private theorem actual_final_bounds {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (s : Bool) :
    (1/4 ≤ C (P x) s-k (P x) s+(8/5)*(P x*w^2)-actualB x w s) ∧
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      Certificates.h (1-x) ≤ C (P x) s-k (P x) s+(8/5)*(P x*w^2)-actualB x w s*q+
        (13/25)*(k (P x) s-(C (P x) s*psi (P x) q-(1-q))) := by
  by_cases hside : s = true ∨ 1-x ≥ 1/2
  · have hy := Certificates.Y_actual_bounds hx0 hx s hside
    have hbase := ScalarTransfer.Y_le_base (k := Certificates.k (1-x)) (x := x) (w := w) (P_nonneg x) s
    have hn := proxy_N hx0 hx s
    have hb := actualB_nonneg hx0 hw0 s
    have hcommon : ScalarTransfer.Y (P x) (Certificates.k (1-x)) x s ≤
        C (P x) s-k (P x) s+(8/5)*(P x*w^2)-actualB x w s := by
      dsimp only [ScalarTransfer.stdB, actualB] at hbase ⊢
      nlinarith only [hbase, hn]
    refine ⟨hy.2.trans hcommon, ?_⟩
    intro q hq0 hq
    have hgap := centering_gap_nonneg (P_nonneg x) (P_le_half hx0) hq s
    have hbq := mul_le_of_le_one_right hb hq
    linarith [hy.1.trans hcommon]
  · have hs : s = false := by cases s <;> simp_all
    subst s
    have hX : 1-x ≤ 1/2 := by by_contra h; exact hside (Or.inr (by linarith))
    have hy := Certificates.Yprime_actual_bounds hx0 hx hX
    have hbase := ScalarTransfer.Yprime_le_base (k := Certificates.k (1-x)) (w := w) (P_nonneg x) hw hX
    have hk := Certificates.k_envelope hx0 hx
    have hcommon : ScalarTransfer.Yprime (P x) (Certificates.k (1-x)) x ≤
        1-Certificates.k (1-x)+(8/5)*(P x*w^2)-actualB x w false := by
      simpa only [actualB, ScalarTransfer.stdB, mul_assoc] using hbase
    constructor
    · norm_num [C, k]
      linarith [hy.2.trans hcommon]
    · intro q hq0 hq
      have hp : P x ≤ actualB x w false := by
        have hp0 := P_nonneg x
        have hxw : 1 ≤ 2*(x+w) := by linarith
        have hn := mul_le_mul_of_nonneg_left hxw hp0
        norm_num [actualB, ScalarTransfer.bit]
        nlinarith only [hn]
      have hab := kappa_absorb (P_nonneg x) (actual_P_small hx0 hx hX) hp hq0 hq
      norm_num [C, k]
      nlinarith only [hy.1, hcommon, hk, hab]

private theorem actual_charge_proxy {x w r : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool) :
    0 ≤ ChargeTransfer.charge (P x) (A x) (Certificates.k (1-x))
      (Certificates.H s (1-x)) x w r s := by
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  have hp0 : 0 ≤ Certificates.p (1-x) := by linarith [Certificates.p_lower hX0 hX]
  have hp1 : Certificates.p (1-x) ≤ 1/2 := by linarith [Certificates.p_upper hX0 hX]
  have ha0 := Certificates.v_lower hX0 hX
  have ha1 : Certificates.v (1-x) ≤ 2 := by linarith [Certificates.v_upper hX0 hX]
  have hk0 : 0 ≤ Certificates.k (1-x) := by linarith [Certificates.k_lower hX0 hX]
  have hk1 : Certificates.k (1-x) ≤ 1/5 := by linarith [Certificates.k_upper hX0 hX]
  have hH0 : 0 ≤ Certificates.H s (1-x) := by
    have hh := Certificates.h_lower hX0 hX
    cases s <;> norm_num [Certificates.H]; linarith
  have hH1 : Certificates.H s (1-x) ≤ 2/5 := by
    have hh := Certificates.h_upper hX0 hX
    cases s <;> norm_num [Certificates.H]; linarith
  have he := ChargeTransfer.charge_error hp0 hp1 (P_nonneg x) (P_le_half hx0)
    ha0 ha1 (one_le_A hx0) (A_le_two hx) hk0 hk1 hH0 hH1 hx0 hw0
    (show x+w ≤ 1 by linarith) hr0 hr (Certificates.p_approximation hx0 hx)
    (show |Certificates.v (1-x)-A x| ≤ 2*(3/400000) by
      convert Certificates.a_approximation hx0 hx using 1; norm_num) s
  have hm := Certificates.polynomial_charge_margin hX0 hX hw0 hw hr0 hr s
  simp only [sub_sub_cancel] at hm
  have hρ : 0 ≤ r+w^2 := add_nonneg hr0 (sq_nonneg w)
  have he' := (abs_le.mp he).2
  nlinarith only [hm, he', hρ]

private theorem actual_charge {x w r : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool) :
    0 ≤ ((C (P x) s*H (Certificates.h (1-x)) s-actualB x w s)*r+(8/5)*(P x*w^2))*
      M (P x) (A x+2*P x*w) s r+
      (C (P x) s-k (P x) s-C (P x) s*H (Certificates.h (1-x)) s*r)*
        L (P x) (m x) (P x*w^2) (actualB x w) s r := by
  have hc := actual_charge_proxy hx0 hx hw0 hw hr0 hr s
  have hl := actual_L hx0 hx hw0 hw s hr0 hr
  have hcoef : 0 ≤ (1-ScalarTransfer.bit s)*Certificates.k (1-x)-k (P x) s := by
    have hk := Certificates.k_envelope hx0 hx
    cases s <;> norm_num [ScalarTransfer.bit, k]; linarith
  have hmul := mul_nonneg hcoef hl
  have hid :
      ((C (P x) s*H (Certificates.h (1-x)) s-actualB x w s)*r+(8/5)*(P x*w^2))*
        M (P x) (A x+2*P x*w) s r+
        (C (P x) s-k (P x) s-C (P x) s*H (Certificates.h (1-x)) s*r)*
          L (P x) (m x) (P x*w^2) (actualB x w) s r =
      ChargeTransfer.charge (P x) (A x) (Certificates.k (1-x)) (Certificates.H s (1-x)) x w r s+
        ((1-ScalarTransfer.bit s)*Certificates.k (1-x)-k (P x) s)*
          L (P x) (m x) (P x*w^2) (actualB x w) s r := by
    cases s <;> norm_num [ChargeTransfer.charge, ChargeTransfer.F1, ChargeTransfer.F2,
      ChargeTransfer.F3, ChargeTransfer.F4, ChargeTransfer.c, ChargeTransfer.bit,
      C, H, k, M, L, m, actualB, ScalarTransfer.bit, Certificates.H] <;> ring
  rw [hid]
  exact add_nonneg hc hmul

theorem actual_scalar_bounds {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) :
    ScalarBounds (P x) (m x) (A x+2*P x*w) (P x*w^2) (Certificates.h (1-x)) (actualB x w) := by
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  refine ⟨P_nonneg x, P_le_half hx0, m_nonneg x, ?_, ?_, ?_,
    actualB_nonneg hx0 hw0, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (P_nonneg x) (sq_nonneg w)
  · linarith [Certificates.h_lower hX0 hX]
  · linarith [Certificates.h_upper hX0 hX]
  · intro s r hr0 hr
    exact actual_first hx0 hx hw0 hw s hr0 hr
  · intro s r hr0 hr
    refine ⟨actual_L hx0 hx hw0 hw s hr0 hr, ?_, actual_linear hx0 hx hw0 hw s hr0 hr⟩
    have hb := actualB_nonneg hx0 hw0 s
    have hq := (actual_final_bounds hx0 hx hw0 hw s).1
    have hbr := mul_le_of_le_one_right hb hr
    unfold K
    linarith only [hq, hbr]
  · intro s r hr0 hr
    exact actual_charge hx0 hx hw0 hw hr0 hr s
  · intro s q hq0 hq
    exact (actual_final_bounds hx0 hx hw0 hw s).2 q hq0 hq
  · intro s
    exact (actual_final_bounds hx0 hx hw0 hw s).1

theorem finite_comparison {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → ℝ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1) (_hR0 : ∀ i, 0 ≤ R i)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i*(1-P x*q i t) ≤ D i+D t) :
    average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) ≤
      2*(P x*(y-x)^2/y) := by
  let w := max 0 (y-x)
  have hw0 : 0 ≤ w := le_max_left _ _
  have hw : w ≤ 1-x := max_le (by linarith) (by linarith)
  have hyy : y ≤ x+w := by have h := le_max_right 0 (y-x); dsimp [w]; linarith
  have ha : A x+2*P x*w = 1+m x+2*P x*(x+w) := by unfold m; ring
  have hbs : actualB x w = fun s => (2-endpoint s)*P x*(x+w) := rfl
  have sb := actual_scalar_bounds hx0 hx hw0 hw
  rw [ha, hbs] at sb
  have hfinite := finite_raw_of_scalar sb hπ0 hπ hD0 hD hq0 hq hs0 hs hcomp
  have hmono : average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) ≤
      average π (fun i => rawRow π D (q i) (P x) (m x) (x+w) (s i) (D i) (R i)) := by
    apply average_mono hπ0
    intro i
    exact rawRow_mono_y hπ0 (P_nonneg x) (hD0 i) (hq0 i) (hq i) (hs i) hyy
  have hz : P x*w^2 ≤ P x*(y-x)^2/y := by
    rcases le_total y x with h | h
    · have hwz : w = 0 := max_eq_left (sub_nonpos.mpr h)
      rw [hwz]
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact div_nonneg (mul_nonneg (P_nonneg x) (sq_nonneg _)) hy0.le
    · have hwe : w = y-x := max_eq_right (sub_nonneg.mpr h)
      rw [hwe]
      exact (le_div_iff₀ hy0).mpr
        (mul_le_of_le_one_right (mul_nonneg (P_nonneg x) (sq_nonneg _)) hy)
  exact hmono.trans (hfinite.trans (mul_le_mul_of_nonneg_left hz (by norm_num)))

end MetricKMedian.FiniteComparison

end
section
end
end

end OAI
