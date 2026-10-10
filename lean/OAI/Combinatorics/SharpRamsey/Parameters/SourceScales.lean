import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.StrongDegreeBudget

namespace OAI

section
section

namespace SharpLogRamsey.ScaleSelection
open Filter Real
open scoped Topology
open SharpLogRamsey.MomentBudgetBridge

theorem eventually_polynomial_le_exp_rpow (C a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ Real.exp (c*x^b) := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound (show 0 < (1/(|C|+1) : ℝ) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    C*x^a ≤ (|C|+1)*x^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx0.le _)
    _ ≤ (|C|+1)*((1/(|C|+1))*Real.exp (c*x^b)) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ = _ := by field_simp

theorem eventually_polynomial_exp_neg_rpow_lt (C a b c ε : ℝ)
    (hb : 0 < b) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a*Real.exp (-c*x^b) < ε := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound
    (show 0 < ε/(2*(|C|+1)) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    _ ≤ (|C|+1)*x^a*Real.exp (-c*x^b) := by
      gcongr
    _ ≤ (|C|+1)*(ε/(2*(|C|+1))*Real.exp (c*x^b))*Real.exp (-c*x^b) := by
      gcongr
    _ = ε/2 := by
      rw [mul_assoc (|C|+1), mul_assoc, ← Real.exp_add,
        show c*x^b+-c*x^b=0 by ring, Real.exp_zero]
      field_simp
    _ < ε := by linarith

def majorant (x : ℝ) : ℝ :=
  1+4*(x^2)^2+4*(x^2)^3*(202*x^2)+(x^2)^4*(202*x^2)^2+
    (x^2)^4*(x^2+4)*(2*x^2)^200

theorem certificate_le_majorant (x P : ℝ) (p D : ℕ) (hx : 1 ≤ x)
    (hP : 0 ≤ P) (hP' : P ≤ x^2) (hp : (p : ℝ) ≤ x^2) (hD : (D : ℝ) ≤ x^2) :
    certificateOverhead p D P ≤ majorant x := by
  have hA : anchorBudget p P ≤ 202*x^2 := by unfold anchorBudget; linarith
  have hA0 : 0 ≤ anchorBudget p P := anchorBudget_nonneg p hP
  unfold certificateOverhead majorant
  gcongr

theorem majorant_le (x : ℝ) (hx : 1 ≤ x) :
    majorant x ≤ (1+4+808+40804+5*2^200 : ℝ)*x^410 := by
  have hx0 : 0 ≤ x := by linarith
  have h0 : (1 : ℝ) ≤ x^410 := one_le_pow₀ hx
  have h4 : x^4 ≤ x^410 := pow_le_pow_right₀ hx (by decide)
  have h8 : x^8 ≤ x^410 := pow_le_pow_right₀ hx (by decide)
  have h12 : x^12 ≤ x^410 := pow_le_pow_right₀ hx (by decide)
  have hD : x^2+4 ≤ 5*x^2 := by nlinarith [sq_nonneg (x-1)]
  have hm : (x^2)^4*(x^2+4)*(2*x^2)^200 ≤ 5*2^200*x^410 := by
    calc
      _ ≤ (x^2)^4*(5*x^2)*(2*x^2)^200 := by gcongr
      _ = _ := by ring
  have he : majorant x = 1+4*x^4+808*x^8+40804*x^12+
      (x^2)^4*(x^2+4)*(2*x^2)^200 := by unfold majorant; ring
  rw [he]
  nlinarith only [h0, h4, h8, h12, hm]

theorem eventually_certificate_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p D : ℕ) (P : ℝ),
    (p : ℝ) ≤ x^2 → (D : ℝ) ≤ x^2 → x^b ≤ P → P ≤ x^2 →
    certificateOverhead p D P ≤ Real.exp (2*P/25) := by
  have hh := eventually_polynomial_le_exp_rpow
    (1+4+808+40804+5*2^200) 410 b (2/25) hb (by norm_num)
  filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with x hx hx1 p D P hp hD hP hP'
  have hx0 : 0 ≤ x := by linarith
  calc
    _ ≤ majorant x := certificate_le_majorant x P p D hx1
      ((Real.rpow_nonneg hx0 _).trans hP) hP' hp hD
    _ ≤ (1+4+808+40804+5*2^200 : ℝ)*x^410 := majorant_le x hx1
    _ ≤ Real.exp ((2/25)*x^b) := by simpa only [Real.rpow_ofNat] using hx
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_shift_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p D : ℕ) (P : ℝ),
    (p : ℝ) ≤ x^2 → (D : ℝ) ≤ x^2 → x^b ≤ P →
    shiftOverhead p D ≤ Real.exp (2*P/25) := by
  have hh := eventually_polynomial_le_exp_rpow (4+200^200) 402 b (2/25) hb (by norm_num)
  filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with x hx hx1 p D P hp hD hP
  have hx0 : 0 ≤ x := by linarith
  have hm : shiftOverhead p D ≤ (4+200^200 : ℝ)*x^402 := by
    have h0 : (1 : ℝ) ≤ x^402 := one_le_pow₀ hx1
    have hh : (D : ℝ)*(200*(p : ℝ))^200 ≤ 200^200*x^402 := by
      calc
        _ ≤ x^2*(200*x^2)^200 := mul_le_mul hD
          (pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left hp (by norm_num)) 200)
          (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg p)) 200) (sq_nonneg x)
        _ = _ := by ring
    unfold shiftOverhead
    nlinarith only [h0, hh]
  calc
    _ ≤ (4+200^200 : ℝ)*x^402 := hm
    _ ≤ Real.exp ((2/25)*x^b) := by simpa only [Real.rpow_ofNat] using hx
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_position_budgets (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p : ℕ) (P : ℝ),
    (p : ℝ) ≤ x^2 → x^b ≤ P →
    (p : ℝ)^2 ≤ Real.exp (P/10) ∧ 2*(p : ℝ)+3 ≤ Real.exp (P/10) := by
  have hh := eventually_polynomial_le_exp_rpow 1 4 b (1/10) hb (by norm_num)
  have hh' := eventually_polynomial_le_exp_rpow 5 2 b (1/10) hb (by norm_num)
  filter_upwards [hh, hh', eventually_ge_atTop (1 : ℝ)] with x hx hx' hx1 p P hp hP
  have hx0 : 0 ≤ x := by linarith
  have he : Real.exp ((1/10)*x^b) ≤ Real.exp (P/10) := Real.exp_le_exp.mpr (by linarith)
  constructor
  · calc
      _ ≤ (x^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hp _
      _ = x^4 := by ring
      _ ≤ Real.exp ((1/10)*x^b) := by simpa only [one_mul, Real.rpow_ofNat] using hx
      _ ≤ _ := he
  · have h1 : 1 ≤ x^2 := one_le_pow₀ hx1
    calc
      _ ≤ 5*x^2 := by linarith
      _ ≤ Real.exp ((1/10)*x^b) := by simpa only [Real.rpow_ofNat] using hx'
      _ ≤ _ := he

lemma nineteen_twentieth_pow_le (n : ℕ) :
    (19/20 : ℝ)^n ≤ Real.exp (-(n : ℝ)/20) := by
  have hb : (19/20 : ℝ) ≤ Real.exp (-(1/20 : ℝ)) := by
    linarith only [Real.add_one_le_exp (-(1/20 : ℝ))]
  calc
    _ ≤ (Real.exp (-(1/20 : ℝ)))^n := pow_le_pow_left₀ (by norm_num) hb _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem eventually_root_budget (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, ∀ (p R : ℕ), (p : ℝ) ≤ x^2 → x^b ≤ R →
    ∃ h : ℕ, 0 < h ∧ 400 ≤ R ∧ h ≤ (R/2)/400 ∧
      (p : ℝ)*h*(19/20 : ℝ)^(h-1) < 1/2 := by
  have hh := eventually_polynomial_exp_neg_rpow_lt (Real.exp (1/10)) (2+b) b
    (1/16000) (1/2) hb (by norm_num) (by norm_num)
  filter_upwards [hh, (tendsto_rpow_atTop hb).eventually_ge_atTop 1600,
    eventually_ge_atTop (1 : ℝ)] with x hx hxb hx1 p R hp hR
  have hx0 : 0 < x := by linarith
  let h : ℕ := ⌊x^b/800⌋₊
  have hh1 : 1 ≤ h := by
    apply Nat.le_floor
    norm_num
    linarith
  have hhle : (h : ℝ) ≤ x^b/800 := Nat.floor_le (by positivity)
  have hhgt : x^b/800 < (h : ℝ)+1 := Nat.lt_floor_add_one _
  have hhr : 800*h ≤ R := by
    have hcast : (800 : ℝ)*(h : ℝ) ≤ R := by linarith
    exact_mod_cast hcast
  have hnat : ((h-1 : ℕ) : ℝ) = (h : ℝ)-1 := by rw [Nat.cast_sub hh1]; norm_num
  have hp' : (p : ℝ)*h ≤ x^(2+b) := by
    calc
      _ ≤ x^2*x^b := by gcongr; linarith only [hhle, Real.rpow_nonneg hx0.le b]
      _ = _ := by rw [Real.rpow_add hx0]; simp only [Real.rpow_ofNat]
  have he : (19/20 : ℝ)^(h-1) ≤ Real.exp ((1/10)-(1/16000)*x^b) := by
    apply (nineteen_twentieth_pow_le (h-1)).trans
    apply Real.exp_le_exp.mpr
    rw [hnat]
    linarith
  refine ⟨h, by omega, by omega, by omega, ?_⟩
  calc
    _ ≤ x^(2+b)*Real.exp ((1/10)-(1/16000)*x^b) :=
      mul_le_mul hp' he (by positivity) (by positivity)
    _ = Real.exp (1/10)*x^(2+b)*Real.exp (-(1/16000)*x^b) := by
      rw [sub_eq_add_neg, Real.exp_add, neg_mul]
      ring
    _ < _ := hx

end SharpLogRamsey.ScaleSelection
end

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
open SharpLogRamsey.ScaleSelection SharpLogRamsey.MomentBudgetBridge

noncomputable def beta (η : ℝ) : ℝ := η/10000000
noncomputable def scaleL (σ η D : ℝ) : ℝ := D*σ^(8*beta η)
noncomputable def scaleP (σ η D : ℝ) (R : ℕ) : ℝ := scaleL σ η D*R

structure Admissible (σ η D : ℝ) (R : ℕ) : Prop where
  D_lower : σ^beta η ≤ D
  D_upper : D ≤ σ^(1-η/2)
  R_lower : σ^beta η ≤ (R : ℝ)
  R_upper : (R : ℝ) ≤ 2*σ^beta η+2
  R_even : Even R

lemma beta_pos {η : ℝ} (hη : 0 < η) : 0 < beta η := by
  unfold beta
  positivity

lemma exponent_gap {η : ℝ} (hη : 0 < η) : 1-η/2+9*beta η < 1 := by
  unfold beta
  linarith

lemma scale_bounds {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0 < η)
    (h : Admissible σ η D R) :
    σ^(9*beta η) ≤ scaleL σ η D ∧
    σ^(10*beta η) ≤ scaleP σ η D R ∧
    scaleP σ η D R ≤ 4*σ^(1-η/2+9*beta η) := by
  have hσ0 : 0 < σ := by linarith
  have hb : 0 < beta η := beta_pos hη
  have hpow : 1 ≤ σ^beta η := Real.one_le_rpow hσ hb.le
  have hD0 : 0 ≤ D := (Real.rpow_nonneg hσ0.le _).trans h.D_lower
  have hL : σ^(9*beta η) ≤ scaleL σ η D := by
    calc
      _ = σ^beta η*σ^(8*beta η) := by rw [← Real.rpow_add hσ0]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.D_lower (Real.rpow_nonneg hσ0.le _)
  refine ⟨hL, ?_, ?_⟩
  · calc
      _ = σ^(9*beta η)*σ^beta η := by rw [← Real.rpow_add hσ0]; congr 1; ring
      _ ≤ scaleL σ η D*(R : ℝ) := mul_le_mul hL h.R_lower
        (Real.rpow_nonneg hσ0.le _) (by unfold scaleL; positivity)
      _ = _ := rfl
  · have hR : (R : ℝ) ≤ 4*σ^beta η := by linarith [h.R_upper]
    calc
      _ ≤ (σ^(1-η/2)*σ^(8*beta η))*(4*σ^beta η) := by
        unfold scaleP scaleL
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.D_upper
          (Real.rpow_nonneg hσ0.le _)) hR (Nat.cast_nonneg _) (by positivity)
      _ = 4*σ^(1-η/2+9*beta η) := by
        rw [mul_assoc, mul_left_comm (σ^(8*beta η)) 4, ← mul_assoc,
          mul_comm (σ^(1-η/2)) 4, mul_assoc, ← Real.rpow_add hσ0,
          ← Real.rpow_add hσ0]
        congr 2
        ring

lemma eventually_monomial_le_linear (C a ε : ℝ) (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-1)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-1))*x := by
      have hp : x^(a-1)*x = x^a := by
        calc
          _ = x^(a-1)*x^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
      rw [mul_assoc, hp]
    _ ≤ ε*x := mul_le_mul_of_nonneg_right hx.le hx0.le

theorem eventually_P_le_linear {η : ℝ} (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
      scaleP σ η D R ≤ ε*σ := by
  filter_upwards [eventually_monomial_le_linear 4 (1-η/2+9*beta η) ε
    (exponent_gap hη) hε, eventually_ge_atTop (1 : ℝ)] with σ hσ hσ1 D R h
  exact (scale_bounds hσ1 hη h).2.2.trans hσ

theorem moment_order_le {σ P : ℝ} {p : ℕ} (hσ : 10002 ≤ σ) (hP : 1 ≤ P)
    (hp : (p : ℝ) ≤ 10000*σ/P+2) : (p : ℝ) ≤ σ^2 := by
  have hσ0 : 0 ≤ σ := by linarith
  have hdiv : 10000*σ/P ≤ 10000*σ := div_le_self (by positivity) hP
  nlinarith [sq_nonneg (σ-10002)]

theorem eventually_enumeration_budgets {η : ℝ} (hη : 0 < η) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R p m : ℕ), Admissible σ η D R →
    (p : ℝ) ≤ 10000*σ/scaleP σ η D R+2 → (m : ℝ) ≤ σ^2 →
    10000 ≤ scaleL σ η D ∧
    certificateOverhead p m (scaleP σ η D R) ≤ Real.exp (2*scaleP σ η D R/25) ∧
    shiftOverhead p m ≤ Real.exp (2*scaleP σ η D R/25) ∧
    (p : ℝ)^2 ≤ Real.exp (scaleP σ η D R/10) ∧
    2*(p : ℝ)+3 ≤ Real.exp (scaleP σ η D R/10) ∧
    ∃ h : ℕ, 0 < h ∧ 400 ≤ R ∧ h ≤ (R/2)/400 ∧
      (p : ℝ)*h*(19/20 : ℝ)^(h-1) < 1/2 := by
  have hb := beta_pos hη
  have h10 : 0 < 10*beta η := by positivity
  have h9 : 0 < 9*beta η := by positivity
  filter_upwards [eventually_certificate_budget (10*beta η) h10,
    eventually_shift_budget (10*beta η) h10,
    eventually_position_budgets (10*beta η) h10,
    eventually_root_budget (beta η) hb,
    (tendsto_rpow_atTop h9).eventually_ge_atTop 10000,
    eventually_P_le_linear hη 1 (by norm_num),
    eventually_ge_atTop (10002 : ℝ)] with σ hc hs hp hr hL hPu hσ D R p m had hp' hm
  have hσ1 : 1 ≤ σ := by linarith
  obtain ⟨hLb, hPb, _⟩ := scale_bounds hσ1 hη had
  have hP1 : 1 ≤ scaleP σ η D R := (Real.one_le_rpow hσ1 h10.le).trans hPb
  have hpm : (p : ℝ) ≤ σ^2 := moment_order_le hσ hP1 hp'
  have hP2 : scaleP σ η D R ≤ σ^2 := by
    have := hPu D R had
    nlinarith [sq_nonneg (σ-1)]
  obtain ⟨hp2, hps⟩ := hp p (scaleP σ η D R) hpm hPb
  exact ⟨hL.trans hLb, hc p m _ hpm hm hPb hP2,
    hs p m _ hpm hm hPb, hp2, hps, hr p R hpm had.R_lower⟩

end SharpLogRamsey.SourceScales
end

end

end OAI
