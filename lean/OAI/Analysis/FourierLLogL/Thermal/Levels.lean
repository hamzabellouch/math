import OAI.Analysis.FourierLLogL.Thermal.GridFreq

/-! # Asymptotic scales for the dyadic bound -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

def H (j : ℕ) : ℝ := slow j

def plateErr (j : ℕ) : ℝ := height j/H j^400
/-- Index depth i denotes b=2^{-i}; b₀=h^{-16}. -/
def mainIx (j : ℕ) := 16*ell j
def testIx (j : ℕ) := mainIx j+3
def beta (i : ℕ) := side i^2/100
/-- Linear growth is enough for the normalization coding sizes -/
def kappa (j : ℕ) (A0 : ℝ) (i : ℕ) := A0 * height j / H j * (1+i)
def eps : ℝ := 1/10000

lemma H_ge (j : ℕ) : 1 ≤ H j := by unfold H; exact_mod_cast slow_pos j
lemma H_pos (j : ℕ) : 0 < H j := lt_of_lt_of_le zero_lt_one (H_ge j)
lemma d_pos (j : ℕ) : 0 < height j := by unfold height; positivity
lemma beta_pos (i : ℕ) : 0 < beta i := by unfold beta; have := side_pos i; positivity
lemma beta_le (i : ℕ) : beta i ≤ 1 := by unfold beta; nlinarith [side_le i, side_pos i]
lemma eps_pos : 0 < eps := by norm_num [eps]
lemma kappa_pos (A0 : ℝ) (hA : 0 < A0) (j i : ℕ) : 0 < kappa j A0 i := by
  unfold kappa; have := H_pos j; have := d_pos j; positivity

lemma beta_log (i : ℕ) : -log (beta i) ≤ 100 + 2*i := by
  rw [beta,Real.log_div (by have := side_pos i; positivity) (by norm_num),
      side_pow_two,Real.log_pow,Real.log_inv,Real.log_pow]
  push_cast
  nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),
    Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100),Nat.cast_nonneg (α:=ℝ) i]

lemma h_large (A : ℝ) : ∀ᶠ j : ℕ in atTop, A ≤ H j := by
  obtain ⟨n,hn⟩ := exists_nat_gt A
  filter_upwards [slow_tendsto.eventually (eventually_ge_atTop n)] with j hj
  exact hn.le.trans (show (n:ℝ)≤ slow j from Nat.cast_le.mpr hj)

lemma hpow_index (A : ℝ) (n : ℕ) : ∀ᶠ j : ℕ in atTop, A*H j^n ≤ (j:ℝ) := by
  filter_upwards [wide_le_j,eventually_pow_small_slow n A] with j hj h
  exact h.trans (by exact_mod_cast hj)

lemma hpoly (A : ℝ) (n : ℕ) :
    ∀ᶠ j : ℕ in atTop, A*H j^n ≤ height j := by
  filter_upwards [hpow_index A n, eventually_pow_small 1 1] with j hh h
  exact hh.trans (by simp only [pow_one,one_mul] at h; exact h)

lemma hpoly_mix (A : ℝ) (n m : ℕ) :
    ∀ᶠ j : ℕ in atTop, A*H j^n*(j:ℝ)^m ≤ height j := by
  filter_upwards [hpow_index A n,eventually_pow_small (m+1) 1] with j hh h
  refine (mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (j:ℝ)^m)).trans ?_
  rwa [pow_succ,one_mul,mul_comm] at h

lemma bottom_level (j : ℕ) : side (mainIx j) = 1/H j^16 := by
  simp only [side_pow_two,H,slow,mainIx,Nat.cast_pow,Nat.cast_ofNat,← pow_mul,one_div,mul_comm 16]

lemma main_bounds (j : ℕ) {i : ℕ} (hi : i ≤ testIx j) :
    ((1/6400)/H j^32 ≤ beta i) ∧ (i:ℝ) ≤ 19*H j ∧
      -log (beta i) ≤ 200*H j := by
  have hX : i ≤ 19*slow j := by
    have hx := ell_le_h j; have h' := slow_pos j
    unfold testIx mainIx at hi; omega
  have hx : (i:ℝ) ≤ 19*H j := by unfold H; exact_mod_cast hX
  have hn := H_ge j
  have hi : side (testIx j) ≤ side i :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
  have he : side (testIx j) = side (mainIx j)/8 := by simp [side,testIx,pow_add]; ring
  refine ⟨?_,hx,by linarith [beta_log i]⟩
  unfold beta
  calc
    _ = side (testIx j)^2/100 := by rw [he,bottom_level]; unfold H; ring
    _ ≤ _ := by have := side_pos (testIx j); gcongr

lemma sigma_small :
    ∀ᶠ j : ℕ in atTop, ∀ i, i ≤ testIx j → 8*sig j ≤ side i^2 := by
  filter_upwards [h_large 1000] with j hj i hi
  have hn := (main_bounds j hi).1
  unfold beta at hn
  change 8*(1/H j^40) ≤ _
  have he : 8*(1/H j^40) ≤ 100*((1/6400)/H j^32) := by
    have hh : H j ≤ H j ^ 8 := by
      have := pow_le_pow_right₀ (by linarith : 1 ≤ H j) (show 1 ≤ 8 by omega)
      simpa using this
    have hc : 512 ≤ H j ^ 8 := by linarith
    have := H_pos j
    rw [show H j^40=H j^8 * H j^32 by ring]
    apply (mul_le_mul_iff_left₀ (show 0 < H j^32 by positivity)).mp
    field_simp
    nlinarith
  linarith

lemma Tk_bounds :
    ∀ᶠ j : ℕ in atTop,
      (sLen j:ℝ)* H j ^6 = height j ∧ 0 < sLen j := by
  filter_upwards [t_expr] with j hj
  constructor
  · unfold H height; exact_mod_cast hj.1
  · exact pow_pos_nat _

lemma kappa_scales (A0 : ℝ) (hA : 1 ≤ A0) :
    ∀ᶠ j : ℕ in atTop, ∀ i, i ≤ testIx j →
      height j/H j^2 ≤ eps*kappa j A0 i ∧ kappa j A0 i ≤ height j ∧
      A0 * height j / H j ≤ kappa j A0 i ∧ 100 ≤ kappa j A0 i := by

  filter_upwards [ell_tendsto.eventually (eventually_pow_small 1 (20*A0)),
    ell_tendsto.eventually (eventually_ge_atTop 1),h_large 10000,hpoly 100 2]
    with j he he' hj hh i hi
  let x := H j; let d := height j
  have hx : 10000 ≤ x := hj
  have hx' : 0 < x := H_pos j
  have hd : 0 < d := d_pos j
  have hk3 : A0 * height j / H j ≤ kappa j A0 i := by
    unfold kappa; have hp : 0 < A0*d/x := div_pos (mul_pos (by linarith) hd) hx'
    exact le_mul_of_one_le_right hp.le (le_add_of_nonneg_right (by positivity))
  refine ⟨le_trans ?_ (mul_le_mul_of_nonneg_left hk3 eps_pos.le),?_,hk3, le_trans ?_ hk3⟩
  · change d/x^2 ≤ 1/10000*(A0*d/x)
    apply (div_le_iff₀ (sq_pos_of_pos hx')).mpr
    rw [show 1/10000*(A0*d/x)*x^2 = (A0*x/10000)*d by field_simp]
    have hi : 10000 ≤ A0*x := by nlinarith
    nlinarith
  · have hI : i+1 ≤ 20*ell j := by unfold testIx mainIx at hi; omega
    have hX : A0*(1+(i:ℝ)) ≤ x := by
      have hE : 20*A0*(ell j) ≤ x := by
        unfold x H slow; push_cast; simpa using he
      have hx2 : (i:ℝ)+1 ≤ 20*ell j := by exact_mod_cast hI
      nlinarith
    unfold kappa
    change A0*d/x*(1+i) ≤ d
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hx').mpr
    exact le_trans (le_of_eq (by ring : A0*d*((1:ℝ)+i)=d*(A0*(1+i))))
      ((mul_le_mul_of_nonneg_left hX hd.le).trans (le_of_eq rfl))
  · change 100 ≤ A0*d/x; apply (le_div_iff₀ hx').mpr
    change _ ≤ d at hh
    change 100*x^2 ≤ d at hh
    nlinarith

lemma stiff_budget (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop, C*H j*(plateErr j + 1000*H j)+2000 ≤ height j/H j^4 := by
  filter_upwards [h_large (2*C),hpoly (10000*C) 6] with j h h'
  let d := height j; let a := H j
  have ha : 2*C ≤ a := h
  have Ha : 1 ≤ a := H_ge _
  have ha' : 0 < a := H_pos _
  have hd : 0 < d := d_pos _
  change 10000*C*a^6 ≤ d at h'
  change C*a*(d/a^400+1000*a)+2000 ≤ d/a^4
  apply (le_div_iff₀ (pow_pos ha' _)).mpr
  have he : a^6 ≤ a^400 := pow_le_pow_right₀ Ha (by omega)
  have he1 : C*a*(d/a^400)*a^4 ≤ d/2 := by
    calc
      _ ≤ (a/2)*a*(d/a^6)*a^4 := by gcongr; linarith
      _ = _ := by field_simp
  have he2 : C*a*(1000*a)*a^4+2000*a^4 ≤ d/2 := by
    rw [show C*a*(1000*a)*a^4=1000*C*a^6 by ring]
    have hg : a^4 ≤ C*a^6 := le_trans (pow_le_pow_right₀ Ha (by omega))
      (le_mul_of_one_le_left (by positivity) hC)
    linarith
  rw [mul_add,add_mul, add_mul]; linarith

end FourierLLogL.Dyadic.Thermal

end OAI
