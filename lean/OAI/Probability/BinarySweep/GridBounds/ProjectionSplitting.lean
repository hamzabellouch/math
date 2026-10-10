import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.SchattenTriangle

namespace OAI

noncomputable section

section

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

lemma projection_sandwich_split (X Y P : M ι) (R : α → M ι) (C : β → M ι)
    (hR : ∀a, R a*R a=R a) (hC : ∀b, C b*C b=C b)
    (hsR : ∑a, R a=1) (hsC : ∑b, C b=1) :
    Y*P*X = ∑b, ∑a, (Y*C b)*(C b*P*R a)*(R a*X) := by
  have he (a : α) (b : β) : (Y*C b)*(C b*P*R a)*(R a*X)=Y*C b*P*R a*X := by
    simp only [mul_assoc,← mul_assoc (C b) (C b),hC b,
      ← mul_assoc (R a) (R a),hR a]
  simp_rw [he]
  simp only [← Finset.sum_mul,← Finset.mul_sum,hsR,hsC,mul_one]

theorem schatten_projection_split {q : ℕ} (hq : 0<q)
    (X Y P : M ι) (R : α → M ι) (C : β → M ι)
    (hR : ∀a, R a*R a=R a) (hC : ∀b, C b*C b=C b)
    (hsR : ∑a, R a=1) (hsC : ∑b, C b=1) :
    schatten q (Y*P*X) ≤ ∑b, ∑a,
      schatten q (Y*C b)*‖C b*P*R a‖*schatten q (R a*X) := by
  rw [projection_sandwich_split X Y P R C hR hC hsR hsC]
  apply (schatten_sum_le hq _).trans
  apply Finset.sum_le_sum
  intro b _
  apply (schatten_sum_le hq _).trans
  exact Finset.sum_le_sum fun a _ => schatten_sandwich hq _ _ _

theorem matrixMoment_projection_split_bound {q : ℕ} (hq : 0<q)
    (X Y P : M ι) (R : α → M ι) (C : β → M ι)
    (hR : ∀a, R a*R a=R a) (hC : ∀b, C b*C b=C b)
    (hsR : ∑a, R a=1) (hsC : ∑b, C b=1)
    (B : ℝ) (hB : 0≤B)
    (hterm : ∀a b, matrixMoment q (Y*C b)*‖C b*P*R a‖^(2*q)*
      matrixMoment q (R a*X) ≤ B^(2*q)) :
    matrixMoment q (Y*P*X) ≤ ((Fintype.card α*Fintype.card β:ℕ):ℝ)^(2*q)*B^(2*q) := by
  have ht (a : α) (b : β) :
      schatten q (Y*C b)*‖C b*P*R a‖*schatten q (R a*X) ≤ B := by
    apply (pow_le_pow_iff_left₀
      (mul_nonneg (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _)) (schatten_nonneg _ _))
      hB (by omega : 2*q≠0)).mp
    simpa only [mul_pow,schatten_pow hq] using hterm a b
  have hs : schatten q (Y*P*X) ≤ ((Fintype.card α*Fintype.card β:ℕ):ℝ)*B := by
    apply (schatten_projection_split hq X Y P R C hR hC hsR hsC).trans
    calc
      _ ≤ ∑b : β, ∑a : α, B := Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => ht a b
      _ = _ := by simp [mul_comm,mul_assoc]
  have hh := pow_le_pow_left₀ (schatten_nonneg _ _) hs (2*q)
  simpa only [schatten_pow hq,mul_pow] using hh

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder

lemma overlap_power_le {x c L : ℝ} {q : ℕ} (hx : 0≤x) (hx1 : x≤1)
    (hc : 0≤c) (hcq : c≤q) (hq : 0<q) (hL : x^2≤Real.exp L) :
    x^(2*q)≤Real.exp (c*L) := by
  by_cases hz : x=0
  · rw [hz,zero_pow (by omega : 2*q≠0)]
    exact (Real.exp_pos _).le
  have hp : 0<x := lt_of_le_of_ne hx (Ne.symm hz)
  have hl : Real.log x≤0 := Real.log_nonpos hp.le hx1
  have he : 2*Real.log x≤L := by
    have hh := Real.log_le_log (sq_pos_of_pos hp) hL
    simpa only [Real.log_pow,Real.log_exp,Nat.cast_ofNat] using hh
  calc
    x^(2*q) = Real.exp (((2*q:ℕ):ℝ)*Real.log x) := by
      rw [Real.exp_nat_mul,Real.exp_log hp]
    _ ≤ Real.exp (c*L) := by
      apply Real.exp_le_exp.mpr
      calc
        ((2*q:ℕ):ℝ)*Real.log x = (q:ℝ)*(2*Real.log x) := by push_cast; ring
        _ ≤ c*(2*Real.log x) := mul_le_mul_of_nonpos_right hcq (by linarith)
        _ ≤ c*L := mul_le_mul_of_nonneg_left he hc

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

theorem matrixMoment_dense_exponential {q : ℕ} (hq : 0<q)
    (X Y P : M ι) (R : α → M ι) (C : β → M ι)
    (hR : ∀a, R a*R a=R a) (hC : ∀b, C b*C b=C b)
    (hsR : ∑a, R a=1) (hsC : ∑b, C b=1)
    (FR : α → ℝ) (FC : β → ℝ) (c F H Echild Eoverlap : ℝ)
    (hc : 0≤c) (hcq : c≤q)
    (hchild : ∀a b, matrixMoment q (Y*C b)*matrixMoment q (R a*X) ≤
      Real.exp (-c*(FR a+FC b)+Echild))
    (hoverlap : ∀a b, ‖C b*P*R a‖^2≤Real.exp (FR a+FC b-F+H+Eoverlap))
    (hcontract : ∀a b, ‖C b*P*R a‖≤1) :
    matrixMoment q (Y*P*X) ≤ ((Fintype.card α*Fintype.card β:ℕ):ℝ)^(2*q)*
      Real.exp (-c*F+Echild+c*H+c*Eoverlap) := by
  let B := -c*F+Echild+c*H+c*Eoverlap
  have hq0 : ((2*q:ℕ):ℝ)≠0 := by exact_mod_cast (by omega : 2*q≠0)
  have he : (Real.exp (B/((2*q:ℕ):ℝ)))^(2*q)=Real.exp B := by
    rw [←Real.exp_nat_mul]
    congr 1
    field_simp
  have ht (a : α) (b : β) :
      matrixMoment q (Y*C b)*‖C b*P*R a‖^(2*q)*matrixMoment q (R a*X) ≤
        (Real.exp (B/((2*q:ℕ):ℝ)))^(2*q) := by
    rw [he]
    calc
      _ = (matrixMoment q (Y*C b)*matrixMoment q (R a*X))*‖C b*P*R a‖^(2*q) := by ring
      _ ≤ Real.exp (-c*(FR a+FC b)+Echild)*
          Real.exp (c*(FR a+FC b-F+H+Eoverlap)) :=
        mul_le_mul (hchild a b)
          (overlap_power_le (norm_nonneg _) (hcontract a b) hc hcq hq (hoverlap a b))
          (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
      _ = Real.exp B := by rw [←Real.exp_add]; congr 1; dsimp [B]; ring
  have hh := matrixMoment_projection_split_bound hq X Y P R C hR hC hsR hsC
    (Real.exp (B/((2*q:ℕ):ℝ))) (Real.exp_pos _).le ht
  rw [he] at hh
  exact hh

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
