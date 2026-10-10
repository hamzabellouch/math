import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogShiftBound
import Mathlib.Algebra.BigOperators.Module

namespace OAI

/-! A decreasing positive weight preserves the bound for all prefixes.
This is the finite Abel step for the Dirichlet polynomial. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_telescoping_weights (w : ℕ → ℝ) (H : ℕ) :
    (∑ n∈range H,(w n-w (n+1)))=w 0-w H := by
  induction H with
  | zero => simp
  | succ H ih => rw [sum_range_succ,ih]; ring

theorem halasz_weighted_prefix (f : ℕ → ℂ) (w : ℕ → ℝ) (H : ℕ) (B : ℝ)
    (hw : ∀ n≤H,0≤w n) (hdec : ∀ n<H,w (n+1)≤w n)
    (hB : ∀ n≤H,‖∑ i∈range n,f i‖≤B) :
    ‖∑ n∈range H,(w n:ℂ)*f n‖≤w 0*B := by
  have hB0 : 0≤B := by simpa only [sum_range_zero,norm_zero] using hB 0 (Nat.zero_le H)
  by_cases hH : H=0
  · subst H
    simpa only [sum_range_zero,norm_zero] using mul_nonneg (hw 0 le_rfl) hB0
  have hlast : H-1≤H := Nat.sub_le H 1
  have heq := sum_range_by_parts w f H
  simp only [Complex.real_smul,Complex.ofReal_sub] at heq
  rw [heq]
  calc
    _ ≤ ‖(w (H-1):ℂ)*(∑ n∈range H,f n)‖+
        ‖∑ n∈range (H-1),((w (n+1):ℂ)-(w n:ℂ))*(∑ i∈range (n+1),f i)‖ := norm_sub_le _ _
    _ ≤ w (H-1)*B+∑ n∈range (H-1),(w n-w (n+1))*B := by
      apply add_le_add
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw _ hlast)]
        exact mul_le_mul_of_nonneg_left (hB H le_rfl) (hw _ hlast)
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro n hn
        have hnH : n<H := by have := mem_range.mp hn; omega
        have hdiff : 0≤w n-w (n+1) := sub_nonneg.mpr (hdec n hnH)
        rw [← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (hdec n hnH)),neg_sub]
        exact mul_le_mul_of_nonneg_left (hB (n+1) (by omega)) hdiff
    _ = w 0*B := by rw [← sum_mul,halasz_telescoping_weights]; ring

lemma halasz_cpow_real_phase {x : ℝ} (hx : 0<x) (s : ℂ) :
    (x:ℂ)^(-s)=(x^(-s.re):ℝ)*
      Complex.exp (Complex.I*((-s.im*Real.log x:ℝ):ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Real.rpow_def_of_pos hx,Complex.ofReal_exp,← Complex.exp_add,
    ← Complex.ofReal_log hx.le]
  congr 1
  apply Complex.ext <;> simp [mul_comm]

theorem halasz_weighted_log_prefix {x : ℝ} (hx : 0<x) (s : ℂ) (hσ : 0≤s.re)
    (H : ℕ) (B : ℝ)
    (hB : ∀ n≤H,‖∑ i∈range n,Complex.exp
      (Complex.I*((-s.im*Real.log (x+i):ℝ):ℂ))‖≤B) :
    ‖∑ n∈range H,((x+n:ℝ):ℂ)^(-s)‖≤x^(-s.re)*B := by
  have heq : (∑ n∈range H,((x+n:ℝ):ℂ)^(-s))=
      ∑ n∈range H,((x+n)^(-s.re):ℝ)*Complex.exp
        (Complex.I*((-s.im*Real.log (x+n):ℝ):ℂ)) := by
    apply sum_congr rfl
    intro n _
    exact halasz_cpow_real_phase (by positivity) s
  rw [heq]
  have h := halasz_weighted_prefix
    (fun n => Complex.exp (Complex.I*((-s.im*Real.log (x+n):ℝ):ℂ)))
    (fun n => (x+n)^(-s.re)) H B
    (fun n _ => Real.rpow_nonneg (by positivity) _)
    (fun n _ => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by push_cast; linarith) (neg_nonpos.mpr hσ)) hB
  simpa only [Nat.cast_zero,add_zero] using h

end TwoPointCorrelations

end OAI
