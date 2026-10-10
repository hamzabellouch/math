import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourceTrainingScales

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology

lemma dyadic_class_count {q : ℕ} {σ : ℝ} (_hq : 0<q) (hex : exp σ=(q:ℝ)) :
    ((Nat.log 2 q+1:ℕ):ℝ)≤σ/log 2+1 := by
  have hh := Real.natLog_le_logb q 2
  rw [Real.logb,show log (q:ℝ)=σ by rw [←hex,log_exp]] at hh
  push_cast
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem eventually_heavy_loss {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ q : ℕ,0<q → exp σ=(q:ℝ) →
    ∀ D R,Admissible σ η D R →
      0≤log (200*(Nat.log 2 q+1:ℕ)) ∧
      log (200*(Nat.log 2 q+1:ℕ))≤ scaleKstar σ η D ∧
      log 50+log (4*(Nat.log 2 q+1:ℕ))≤ scaleP σ η D R := by
  have hβ := beta_pos hη
  have hp := ScaleSelection.eventually_polynomial_le_exp_rpow
    (200*(1/log 2+1)) 1 (7*beta η) 1 (by positivity) (by norm_num)
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with σ hp hσ
  intro q hq hex D R had
  have hσp : 0<σ := by linarith
  have h2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hL : (0:ℝ)<(Nat.log 2 q+1:ℕ) := by positivity
  have hcount := dyadic_class_count hq hex
  have hlin : (200*(Nat.log 2 q+1:ℕ):ℝ)≤200*(1/log 2+1)*σ := by
    push_cast at *
    have ha : (Nat.log 2 q:ℝ)+1≤σ*(1/log 2+1) := by
      calc
        _ ≤ σ/log 2+σ := by linarith
        _ = _ := by ring
    nlinarith
  have hlog : log (200*(Nat.log 2 q+1:ℕ))≤σ^(7*beta η) := by
    have he : (200*(Nat.log 2 q+1:ℕ):ℝ)≤exp (σ^(7*beta η)) := by
      apply hlin.trans
      simpa only [rpow_one,one_mul] using hp
    have hh := log_le_log (by positivity : (0:ℝ)<200*(Nat.log 2 q+1:ℕ)) he
    simpa only [log_exp] using hh
  have hK : σ^(7*beta η)≤ scaleKstar σ η D := by
    unfold scaleKstar
    have hh := mul_le_mul_of_nonneg_right had.D_lower (rpow_nonneg hσp.le (6*beta η))
    rw [←rpow_add hσp] at hh
    simpa only [show beta η+6*beta η=7*beta η by ring] using hh
  have hLP : σ^(7*beta η)≤ scaleP σ η D R := by
    have hLL := (scale_bounds hσ hη had).1
    have hlow : σ^(7*beta η)≤σ^(9*beta η) := rpow_le_rpow_of_exponent_le hσ (by linarith)
    have hR : (1:ℝ)≤R := by
      have hrr := had.R_lower
      have hp1 : 1≤σ^beta η := one_le_rpow hσ hβ.le
      linarith
    exact (hlow.trans hLL).trans (le_mul_of_one_le_right (L_pos hσp had).le hR)
  refine ⟨log_nonneg ?_,hlog.trans hK,?_⟩
  · have hh : (1:ℝ)≤(Nat.log 2 q+1:ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
    linarith
  · rw [←log_mul (by norm_num : (50:ℝ)≠0) (by positivity : (4*(Nat.log 2 q+1:ℕ):ℝ)≠0),
      show (50:ℝ)*(4*(Nat.log 2 q+1:ℕ))=200*(Nat.log 2 q+1:ℕ) by ring]
    exact hlog.trans hLP

end SharpLogRamsey.SourceScales

end

end OAI
