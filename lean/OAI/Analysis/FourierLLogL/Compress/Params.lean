import OAI.Analysis.FourierLLogL.Compress.Schedule
/-! # Choice of entropy parameters

Here j tends to infinity, d=2^j. We take h a power of two, comparable with log j. -/
open Set Function Filter
open scoped Topology BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress.Params
open Real
def ell (j : ℕ) := Nat.log 2 (Nat.log 2 j / 1000)
def slow (j : ℕ) : ℕ := 2^ell j
def wide (j : ℕ) : ℕ := 2^slow j
def height (j : ℕ) : ℝ := 2^j
def sLen (j : ℕ) := 2^(j-6*ell j)
def sSeg (j : ℕ) := 2^(j-6*ell j-2)
def long (j : ℕ) := height j * (2:ℝ)^wide j


lemma pow_pos_nat (n : ℕ) : 0 < 2^n := Nat.pow_pos (by omega)

lemma slow_pos (j : ℕ) : 0 < slow j := pow_pos_nat _
lemma ell_tendsto : Tendsto ell atTop atTop := by
  refine tendsto_atTop.2 fun l => ?_
  filter_upwards [eventually_ge_atTop (2^(2^l*1000))] with j hj
  have h := Nat.le_log_of_pow_le (by omega : 1 < 2) hj
  apply Nat.le_log_of_pow_le (by omega : 1 < 2)
  change 2^l ≤ Nat.log 2 j / 1000
  omega

lemma slow_tendsto : Tendsto slow atTop atTop := by
  refine tendsto_atTop_mono (f:=ell) ?_ ell_tendsto
  intro j
  exact (Nat.lt_two_pow_self).le

lemma wide_tendsto : Tendsto wide atTop atTop := by
  refine tendsto_atTop_mono (f:=slow) ?_ slow_tendsto
  intro j
  exact Nat.le_of_lt (Nat.lt_two_pow_self)

lemma evt_slow : ∀ᶠ j : ℕ in atTop,
    2^(1000*slow j) ≤ j ∧ j < 2^(3000*slow j) := by
  filter_upwards [eventually_ge_atTop (2^1000)] with j hj
  have h := Nat.le_log_of_pow_le (by omega : 1 < 2) hj
  have hp := (show 0 < Nat.log 2 j/1000 by omega)
  have h1 : 2^ell j ≤ Nat.log 2 j/1000 := Nat.pow_log_le_self 2 hp.ne'
  have hx := slow_pos j
  have h2 := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (Nat.log 2 j/1000)
  change _ < 2^(ell j+1) at h2
  rw [pow_succ] at h2
  change _ < slow j *2 at h2
  change slow j ≤ _ at h1
  constructor
  · apply le_trans (b:=2^(Nat.log 2 j)) ?_ (Nat.pow_log_le_self 2 (by have := pow_pos_nat 1000; omega))
    apply Nat.pow_le_pow_right (by omega)
    omega
  · apply lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by omega : 1 < 2) j)
    apply Nat.pow_le_pow_right (by omega)
    omega

lemma eventually_pow_small (n : ℕ) (C : ℝ) :
    ∀ᶠ j : ℕ in atTop, C*(j:ℝ)^n ≤ 2^j := by
  have H := (tendsto_pow_const_div_const_pow_of_one_lt n (show (1:ℝ)<2 by norm_num)).const_mul C
  rw [mul_zero] at H
  filter_upwards [H.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with j hj
  apply le_of_lt
  apply (div_lt_one (by positivity : (0:ℝ)<2^j)).mp
  rw [mul_div_assoc]
  exact hj

lemma eventually_pow_small_slow (n : ℕ) (C : ℝ) :
    ∀ᶠ j : ℕ in atTop, C*(slow j:ℝ)^n ≤ 2^slow j :=
  slow_tendsto.eventually (eventually_pow_small n C)

lemma nat_pow_small_slow (n C : ℕ) :
    ∀ᶠ j in atTop, C * (slow j)^n ≤ wide j := by
  filter_upwards [eventually_pow_small_slow n C] with j hj
  unfold wide; exact_mod_cast hj


def base (j : ℕ) : ℕ := 2^(wide j ^ 2)
def capE (j : ℕ) : ℕ := 2^(64*slow j)
def cap (j : ℕ) : ℕ := 2^capE j


lemma wide_le_j : ∀ᶠ j : ℕ in atTop, wide j ≤ j := by
  filter_upwards [evt_slow] with j ⟨hj,h'⟩
  exact le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hj
lemma ell_le_h (j : ℕ) : ell j ≤ slow j := Nat.le_of_lt Nat.lt_two_pow_self
lemma h_le_wide (j : ℕ) : slow j ≤ wide j := Nat.le_of_lt Nat.lt_two_pow_self
lemma slow_le_j : ∀ᶠ j in atTop, slow j ≤ j := wide_le_j.mono fun j h => (h_le_wide j).trans h

lemma base_le_cap (j : ℕ) : base j ≤ cap j := by
  unfold base cap capE wide
  apply Nat.pow_le_pow_right (by omega)
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by omega)
  omega

lemma cap_power : ∀ᶠ j : ℕ in atTop, 64*capE j ≤ j := by
  filter_upwards [evt_slow] with j hj
  apply le_trans (b:=2^(1000*slow j)) _ hj.1
  unfold capE
  rw [show 64 = 2^6 by norm_num]
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by omega)
  have := slow_pos j; omega

lemma below_base (n : ℕ) (C : ℝ) :
    ∀ᶠ j : ℕ in atTop, C * (j:ℝ)^n ≤ base j := by
  obtain ⟨k,hk⟩ := exists_nat_gt C
  filter_upwards [evt_slow, wide_tendsto.eventually (eventually_ge_atTop (max k (4000*n+2)))] with j ⟨hj,h1⟩ h2
  apply le_trans (b:=(k:ℝ)*(j:ℝ)^n) (mul_le_mul_of_nonneg_right hk.le (by positivity))
  suffices H : k*j^n ≤ base j by exact_mod_cast H
  have hk1 : k ≤ wide j := le_trans (le_max_left _ _) h2
  apply le_trans (b:= (2^k)*(2^(3000*slow j))^n) (Nat.mul_le_mul
    (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left h1.le n))
  unfold base
  rw [← pow_mul, ← pow_add]
  apply Nat.pow_le_pow_right (by omega)
  have hx : 4000*n+2 ≤ wide j := le_trans (le_max_right _ _) h2
  nlinarith [h_le_wide j]

lemma t_expr : ∀ᶠ j : ℕ in atTop,
    sLen j * (slow j)^6 = 2^j ∧ 4*sSeg j = sLen j := by
  filter_upwards [evt_slow] with j ⟨h,_⟩
  have h1 := Nat.lt_two_pow_self (n:=1000*slow j)
  have h2 := ell_le_h j
  have h3 := slow_pos j
  constructor
  · unfold sLen slow
    rw [← pow_mul,← pow_add]
    congr 1; omega
  · unfold sSeg sLen
    rw [show 4=2^2 by norm_num,← pow_add]
    congr 1; omega


def nSched (j : ℕ) : ℕ := 2^(16*slow j)
def qSched (j : ℕ) : ℕ := 2*slow j^2
def mSched (j : ℕ) : ℕ := nSched j * (qSched j*nSched j)

def searchSched (j : ℕ) (hj : 4 ≤ slow j) : Schedule := by
  let h : ℝ := slow j
  have hh : 4 ≤ h := by dsimp only [h]; exact_mod_cast hj
  have h' : 0 < h := by linarith
  let N := nSched j; let q := qSched j
  have hn : exp (6*h) ≤ (N:ℝ) := by
    have hi : (1:ℝ)/2 ≤ log 2 := by linarith [Real.log_two_gt_d9]
    have hN : 0 < (N:ℝ) := by exact_mod_cast pow_pos_nat (16*slow j)
    rw [← Real.exp_log hN]
    apply Real.exp_monotone
    dsimp only [N,nSched]; push_cast; rw [Real.log_pow]
    push_cast
    unfold h at *
    nlinarith
  have Hn (k : ℝ) (hk : k ≤ 4) : 1 < N * exp (-k*h) := by
    have H : 0 < 6*h+-k*h := by nlinarith
    calc
      1 < exp (6*h+-k*h) := Real.one_lt_exp_iff.mpr H
      _ = _ := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hn (exp_nonneg _)
  have hq : (q:ℝ)=2*h^2 := by dsimp only [q,h,qSched]; push_cast; rfl
  refine { N := N, n := N, q := q
           N0 := pow_pos_nat _, n0 := pow_pos_nat _, q0 := ?_
           u := 1/h^2, a:= 1/h^3, δ:=exp (-4*h), η:=exp (-2*h)
           α:=32/h^2, ε:=exp (-2*h)
           u0:=by positivity
           a0:=by positivity
           d0:=exp_pos _
           heta:=?_
           hn:= Hn 4 le_rfl
           hα:=by positivity
           hε:=exp_pos _
           hβ:=?_
           hc:=?_
           hq:=?_
           ht:=Hn 2 (by norm_num) }
  · have : (0:ℝ) < q := by rw [hq]; positivity
    exact_mod_cast this
  · rw [← exp_add]
    apply le_of_eq; congr 1; field_simp; ring
  · field_simp; nlinarith
  · rw [show (1/h^3)/(32/h^2) = 1/(32*h) by field_simp]
    rw [hq,add_mul,← exp_add]
    have he : -2*h+ 2*(1/(32*h))*(2*h^2) ≤ -h := by field_simp; nlinarith
    have hx := Real.exp_monotone he
    rw [Real.exp_neg] at hx
    have HH : (exp h)⁻¹ ≤ 1/2 := by
      have := Real.add_one_le_exp h
      rw [inv_le_comm₀ (exp_pos h) (by norm_num)]
      norm_num; linarith
    linarith
  · rw [hq]; field_simp; nlinarith

lemma nSched_scale (j : ℕ) (hj : 4 ≤ slow j) :
    (searchSched j hj).size = mSched j := rfl

lemma searchSched_loss (j : ℕ) (hj : 4 ≤ slow j) :
    (searchSched j hj).loss ≤ 66/(slow j:ℝ)^2 := by
  let h : ℝ := slow j
  have hp : 4 ≤ h := by dsimp only [h]; exact_mod_cast hj
  change 2*(32/h^2)+1/h^3*(1+exp (-2*h)) ≤ 66/h^2
  have HH : exp (-2*h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have : (0:ℝ) < h := by linarith
  field_simp; ring_nf at HH ⊢; nlinarith


def levelLow (j i : ℕ) : ℕ := wide j ^ 2 + 4*wide j*(mSched j-i)
def levelHigh (j i : ℕ) : ℕ := levelLow j i + 3*wide j
def stepLow (j i : ℕ) : ℕ := 2^levelLow j i
def stepHigh (j i : ℕ) : ℕ := 2^levelHigh j i

def stepRows (j i : ℕ) : ℕ := 2^(j-(6*ell j+3+levelLow j i))

lemma index_budgets :
    ∀ᶠ j : ℕ in atTop, ∀ i, levelHigh j i ≤ capE j ∧ 6*ell j+3+levelHigh j i ≤ j := by
  filter_upwards [wide_tendsto.eventually (eventually_ge_atTop 8),cap_power] with j h wj
  let w := wide j
  have hp : 8 ≤ w := h
  have hm : nSched j = w^16 := by
    unfold nSched w wide
    rw [← pow_mul]; congr 1; omega
  have hc : capE j = w^64 := by
    unfold capE w wide
    rw [← pow_mul]; congr 1; omega
  have hb : mSched j ≤ 2*w^34 := by
    rw [mSched,hm,qSched]
    calc
      _ ≤ w^16*(2*w^2*w^16) := by
        have H : slow j ≤ w := h_le_wide j
        gcongr
      _ = _ := by ring
  have hhE : 6*ell j+3 ≤ capE j := by
    have hg : ell j ≤ w := (ell_le_h j).trans (h_le_wide j)
    rw [hc]
    have hh : w^2 ≤ w^64 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  intro i
  have hx : levelHigh j i ≤ capE j := by
    have H1 : mSched j-i ≤ 2*w^34 := le_trans (by omega) hb
    change w^2+4*w*(mSched j-i)+3*w ≤ _
    rw [hc]
    have h₁ : w ≤ w^35 := by
      exact le_trans (by rw [pow_one] : w ≤ w^1) (Nat.pow_le_pow_right (by omega) (by omega))
    have h₂ : w^2 ≤ w^35 := Nat.pow_le_pow_right (by omega) (by omega)
    have h₃ : 16*w^35 ≤ w^64 := by
      have H : 16 ≤ w^29 := le_trans (b:=w^2) (by nlinarith)
        (Nat.pow_le_pow_right (by omega) (by omega))
      apply le_trans (Nat.mul_le_mul_right (w^35) H)
      rw [← pow_add]
    calc
      _ ≤ w^2+4*w*(2*w^34)+3*w := by gcongr
      _ ≤ 16*w^35 := by
        rw [show 4*w*(2*w^34)=8*w^35 by ring]; omega
      _ ≤ _ := h₃
  exact ⟨hx,by omega⟩

lemma array_spec :
    ∀ᶠ j : ℕ in atTop,
    3*sSeg j ≤ sLen j ∧ cap j ≤ sSeg j ∧
    cap j ≤ 2^j ∧
    (∀ i, stepLow j i ≤ stepHigh j i ∧ stepHigh j i ≤ cap j ∧
      2*stepRows j i * stepLow j i = sSeg j ∧
      long j ≤ (stepRows j i:ℝ) * stepHigh j i ∧
      base j ≤ stepLow j i) ∧
    (∀ i k, i < k → k < mSched j →
      stepHigh j k ≤ stepLow j i ∧ stepRows j i ≤ stepRows j k) := by
  filter_upwards [index_budgets,t_expr,nat_pow_small_slow 1 10,
    slow_tendsto.eventually (eventually_ge_atTop 4),cap_power] with j heq ht hw hs hj
  have h1 : 6*ell j+2+capE j ≤ j := by
    have H0 : 6*ell j ≤ levelHigh j 0 := by
      unfold levelHigh levelLow; rw [pow_one] at hw
      have H := ell_le_h j; omega
    have h2 := heq 0
    have hh := pow_pos_nat (64*slow j); change 0 < capE j at hh
    omega
  refine ⟨by omega,?_,?_ ,?_,?_⟩
  · apply Nat.pow_le_pow_right (by omega)
    omega
  · apply Nat.pow_le_pow_right (by omega)
    omega
  · intro i
    have hp := heq i
    have hlow : levelLow j i ≤ levelHigh j i := by unfold levelHigh; omega
    refine ⟨Nat.pow_le_pow_right (by omega) hlow,Nat.pow_le_pow_right (by omega) hp.1,?_,?_,?_⟩
    · unfold stepLow stepRows sSeg
      nth_rw 1 [show 2 = 2^1 by rfl]
      rw [← pow_add,← pow_add]; congr 1; omega
    · unfold long height stepRows stepHigh
      push_cast
      rw [← pow_add, ← pow_add]
      apply pow_le_pow_right₀ (by norm_num)
      unfold levelHigh at *
      rw [pow_one] at hw
      have hh := ell_le_h j
      omega
    · unfold base stepLow
      apply Nat.pow_le_pow_right (by omega)
      unfold levelLow; omega
  intro i k hi hk
  have h1 : levelHigh j k ≤ levelLow j i := by
    unfold levelHigh levelLow
    have h2 : mSched j-k+1 ≤ mSched j-i := by omega
    nlinarith
  constructor
  · exact Nat.pow_le_pow_right (by omega) h1
  · unfold stepRows
    apply Nat.pow_le_pow_right (by omega)
    unfold levelHigh at h1; omega

lemma big_t_real :
    ∀ᶠ j : ℕ in atTop,
      height j = 4*(sSeg j:ℝ)*(slow j:ℝ)^6 ∧
      (cap j:ℝ)^4 ≤ height j := by
  filter_upwards [t_expr,cap_power] with j h h'
  constructor
  · have H : 2^j = 4*sSeg j*slow j^6 := by rw [h.2,h.1]
    unfold height
    exact_mod_cast H
  · have H1 : cap j^4 ≤ (2:ℕ)^j := by
      rw [cap, ← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    unfold height
    exact_mod_cast H1

end FourierLLogL.Compress.Params

end OAI
