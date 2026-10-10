import OAI.Analysis.FourierLLogL.Thermal.Alarm

/-! # Asymptotic evidence in the comparison experiment -/
open Set Function Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

lemma clones_eq (j : ℕ) : (clones j:ℝ)= H j^120 := by
  unfold clones H; push_cast; rfl
lemma clones_pos (j : ℕ) : 0 < clones j := pow_pos (slow_pos _) _

def observationBudget (C : ℝ) (j : ℕ) := 1+C*H j*(1+clones j)

lemma obs_scale (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop, 2+2*observationBudget C j ≤ H j^130 := by
  filter_upwards [h_large (10*C)] with j h
  let a := H j
  have hp := H_ge j
  have hm : (clones j:ℝ)=a^120 := clones_eq _
  unfold observationBudget; rw [hm]
  change 2+2*(1+C*a*(1+a^120)) ≤ a^130
  change 10*C ≤ a at h; change 1 ≤ a at hp
  have h1 : a^122 ≤ a^130 := pow_le_pow_right₀ hp (by omega)
  have h2 : 1 ≤ a^120 := one_le_pow₀ hp
  have h3 : 10*C*a*(a^120) ≤ a^122 :=
    calc
      _ ≤ a*a*a^120 := by gcongr
      _ = _ := by ring
  have hs : 1 ≤ C*a := one_le_mul_of_one_le_of_one_le hC hp
  have h4 : C*a ≤ C*a*a^120 := le_mul_of_one_le_right (by linarith) h2
  linarith

private lemma alarm_scale :
    ∀ᶠ j : ℕ in atTop, ∀ i, i ≤ testIx j → ∀ c : ℝ,
      height j/H j^2 ≤ c →
        log (clones j)+log 4+32+6*cushion j+height j/H j^4 -
          (2*(sLen j):ℕ)*log (beta i/4) ≤ c/8 := by
  filter_upwards [Tk_bounds,h_large 100000,hpoly 1000000 123] with j ⟨hx,hy⟩ hp1 hp2 i hi c hh
  let d := height j; let a := H j
  have h := H_ge j; have hp := H_pos j
  have he := (main_bounds j hi).2.2
  have hz := log_le_sub_one_of_pos (show 0 < (clones j:ℝ) by rw [clones_eq]; positivity)
  rw [clones_eq] at *
  have h4 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  rw [Real.log_div (beta_pos i).ne' (by norm_num)]
  push_cast
  let t : ℝ := sLen j
  have ht : 0 ≤ t := by unfold t; positivity
  change 1 ≤ a at h; change 0 < a at hp; change 100000 ≤ a at hp1
  change t*a^6=d at hx
  change -log (beta i) ≤ 200*a at he
  change 1000000*a^123 ≤ d at hp2
  have h₁ : log (a^120)+log 4+32 ≤ d/(64*a^2) := by
    change log (a^120) ≤ _ at hz
    apply (le_div_iff₀ (by positivity : 0<64*a^2)).mpr
    have hr : a^122 ≤ a^123 := pow_le_pow_right₀ h (by omega)
    calc
      _ ≤ (100*a^120)*(64*a^2) := by gcongr; linarith [one_le_pow₀ h (n:=120)]
      _ ≤ _ := by nlinarith [one_le_pow₀ h (n:=122)]
  have h₂ : 6*d/a^100 + d/a^4 ≤ d/(64*a^2) := by
    have hd : 0 ≤ d := by unfold d; exact (d_pos _).le
    calc
      _ ≤ 6*d/a^4+d/a^4 := by gcongr; norm_num
      _ = 7/(a^4)*d := by ring
      _ ≤ _ := by
        rw [div_eq_mul_inv d,mul_comm d]
        have hi : 7/a^4 ≤ (64*a^2)⁻¹ := by field_simp; nlinarith
        exact mul_le_mul_of_nonneg_right hi hd
  have h₃ : -(2*t)*(log (beta i)-log 4) ≤ d/(64*a^2) := by
    calc
      _ ≤ 500*t*a := by nlinarith
      _ ≤ _ := by
        apply (le_div_iff₀ (by positivity : 0<64*a^2)).mpr
        rw [← hx]
        rw [show 500*t*a*(64*a^2)=t*(32000*a^3) by ring]
        gcongr
        calc
          _ ≤ a*a^3 := by gcongr; linarith
          _ = a^4 := by ring
          _ ≤ _ := pow_le_pow_right₀ h (by omega)
  change log (a^120)+_+32+6*(d/a^100)+d/a^4-2*t*(log _-_) ≤ _
  have ht : d/(64*a^2)*64 ≤ c := by apply le_trans _ hh; exact le_of_eq (by ring)
  rw [← mul_div_assoc]
  have : 0 ≤ d/(64*a^2) := by unfold d; have := d_pos j; positivity
  linarith

/-- Probability form: unnormalized comparison weights are tune × 1_p -/
theorem conditional_bound (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ M : ℕ, ∀ p : Node,
    ∀ A : Form M, Press C j p A → 1000*p.invlen ≤ 2^M →
    ∀ P : Law (Grid M), ∀ u : Update j M p, u.Good C A P →
      u.regular → ∀ s : Profile M,
      (∀ i∈s, 0 ≤ i.1 ∧ i.1 ≤ A) → s.length ≤ observationBudget C j →
      admissible s p (cushion j) → ∀ z : Grid M,
      expU (fun x => prefixE s p x * u.alarmQ A z x) ≤
        exp (-(u.credit/8)) * expU (prefixE s p) := by
  filter_upwards [obs_scale C hC,alarm_scale,paid_tighten C hC] with j h ht hC'
  intro M p A hP hq P u Hu Hr s hS hn hs z
  let a := H j
  let E := u.credit
  let Q := tilde a A p
  have hp := hP.fits
  have hh : 1 ≤ a := H_ge j
  have hA : 0 ≤ A := by obtain ⟨_,_,_,ha,_⟩ := hP.cap; exact ha.nonneg
  have hZ : 2+2*(s.length:ℝ) ≤ a^130 := by linarith [show _ ≤ a^130 from h]
  have hM (x : Grid M) : mixForm s x ≤ s.length*A x := mix_bound (fun i hi => (hS i hi).2) x
  have hR : 0 ≤ p.invlen := p.invlen_pos.le
  have hX : S M (1000*p.invlen) ≤ Q := by
    apply le_add_of_nonneg_left
    intro i; exact mul_nonneg (pow_nonneg (by linarith : 0 ≤ a) _) (hA i)
  have hS' (i) (hi:i∈s) : 0 ≤ i.1 := (hS i hi).1
  have hF₁ : (2:ℝ) • mixForm s ≤ Q := by
    intro i
    have hh := hM i
    have h2 := S_nonneg M (1000*p.invlen) i
    have h3 : 0 ≤ A i := hA i
    change 0 ≤ S M (1000*p.invlen) i at h2
    change 2*mixForm s i ≤ a^130*A i+_
    nlinarith
  have hF₂ : A+place p M+mixForm s ≤ Q := by
    intro i
    have hh := hM i
    have h₂ := S_mono (M:=M) (b:=1000*p.invlen) hR (by linarith) i
    have h3 : 0 ≤ A i := hA i
    change A i+S M _ i + _ ≤ a^130*A i+S M (1000*p.invlen) i
    have hi : 0 ≤ (s.length:ℝ) := by positivity
    nlinarith
  have hlo := posterior_denominator hp hX hq s hs hS' hF₁
  have hhi := u.one_clone_tail hp hA Hu Hr s hS' hF₂ z
  let D := cushion j
  let L := clones j
  let T := 2*sLen j
  let b := beta u.ix/4
  have hL : 0 < (L:ℝ) := by unfold L; exact_mod_cast clones_pos j
  have hb : 0 < b := div_pos (beta_pos _) (by norm_num)
  apply le_of_mul_le_mul_left _ (pow_pos hb T)
  have H₀ : expU (fun x => prefixE s p x * u.alarmQ A z x) ≤
      L * expU (fun x => prefixE s p x * u.singleQ A z x) := by
    rw [expU_ex,expU_ex,← Ex_lmul]; refine Ex_mono _ fun x => ?_
    exact le_trans (mul_le_mul_of_nonneg_left (u.alarm_le _ _ _) (prefixE_nonneg _ _ _)) (le_of_eq (by ring))
  calc
    _ ≤ b^T*(L * expU (fun x => prefixE s p x * u.singleQ A z x)) := by gcongr
    _ ≤ ↑L * exp (32-F (A+place p M)-E/4+4*D) := by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left hhi hL.le
    _ ≤ b^T*(exp (- (E/8)) * (exp (- (2*D)-F Q)/4)) := by
      have hc := exp_pos
      apply le_of_not_gt
      intro he
      have hz₀ := log_lt_log (show 0 < b^T*(exp ( - (E/8))*(exp (- (2*D)-F Q)/4)) by positivity) he
      rw [log_mul,log_pow,log_mul,Real.log_div (x:=exp (-(2*D)-F Q)) (y:=4),log_mul] at hz₀
      · simp_rw [log_exp] at hz₀
        have hY : log (L:ℝ)+ log 4 +32+6*D+height j / a^4 - (T:ℝ)*log b ≤ E/8 :=
          ht u.ix Hu.ix_ok _ Hu.reserves.1
        have hh' : F Q - F (A+place p M) ≤ height j/a^4 := hC' M p A hP
        linarith
      all_goals positivity
    _ ≤ _ := by
      gcongr

end FourierLLogL.Dyadic.Thermal

end OAI
