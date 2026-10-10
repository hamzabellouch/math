import Mathlib
import OAI.Analysis.MatrixSigning.Potential.DerivLine
import OAI.Analysis.MatrixSigning.Potential.QuadraticRemainder

namespace OAI

open Matrix

namespace CurrentKS.Difference

section
open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma line_shift_iteratedDeriv (f : E → ℝ) (x v : E) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun r : ℝ => f ((x+t • v)+r • v)) 0 =
      iteratedDeriv n (fun r : ℝ => f (x+r • v)) t := by
  have he : (fun r : ℝ => f ((x+t • v)+r • v)) =
      (fun r : ℝ => (fun s : ℝ => f (x+s • v)) (t+r)) := by
    funext r
    dsimp only
    rw [add_smul,add_assoc]
  rw [he]
  simpa only [add_zero] using congrFun (iteratedDeriv_comp_const_add n (fun s : ℝ => f (x+s • v)) t) 0

theorem line_quadratic_remainder {f : E → ℝ} {x v : E} {s M : ℝ}
    (hs : 0 < s)
    (hf : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 3 f (x+t • v))
    (hM : ∀ t ∈ Ioo 0 s,
      |iteratedDeriv 3 (fun r : ℝ => f ((x+t • v)+r • v)) 0| ≤ M) :
    |f (x+s • v)-(f x+s*(fderiv ℝ f x v)+
      s^2/2*(fderiv ℝ (fderiv ℝ f) x v v))| ≤ M*s^3/6 := by
  have hline : ContDiff ℝ 3 (fun t : ℝ => x+t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hc : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 3 (fun r : ℝ => f (x+r • v)) t := by
    intro t ht
    exact (hf t ht).comp t hline.contDiffAt
  have h0 := hc 0 (left_mem_Icc.mpr hs.le)
  have h2 : ContDiffAt ℝ 2 f (x+(0:ℝ) • v) :=
    (hf 0 (left_mem_Icc.mpr hs.le)).of_le (by norm_num)
  have hd1 := deriv_line (h2.differentiableAt (by norm_num))
  have hd2 := second_deriv_line h2
  have hbound : ∀ t ∈ Ioo 0 s,
      |iteratedDeriv 3 (fun r : ℝ => f (x+r • v)) t| ≤ M := by
    intro t ht
    simpa only [line_shift_iteratedDeriv] using hM t ht
  have ht := quadratic_remainder hs (fun t ht => (hc t ht).contDiffWithinAt) h0 hbound
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,hd1,hd2,zero_smul,add_zero] using ht

end

open Set
open scoped ContDiff

lemma linear_remainder {f : ℝ → ℝ} {s M : ℝ} (hs : 0 < s)
    (hf : ContDiffOn ℝ 2 f (Icc 0 s)) (hf0 : ContDiffAt ℝ 2 f 0)
    (hM : ∀ t ∈ Ioo 0 s,|iteratedDeriv 2 f t| ≤ M) :
    |f s-(f 0+s*deriv f 0)| ≤ M*s^2/2 := by
  obtain ⟨t,ht,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) (ne_of_lt hs)
    (by norm_num only [Nat.cast_ofNat, Set.uIcc_of_le hs.le]; exact hf)
  simp only [Set.uIoo_of_le hs.le, Set.uIcc_of_le hs.le] at ht he
  have h1 := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs)
    (hf0.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)) (left_mem_Icc.mpr hs.le)
  have hformula : taylorWithinEval f 1 (Icc 0 s) 0 s=f 0+s*deriv f 0 := by
    rw [show 1=0+1 from rfl,taylorWithinEval_succ,taylor_within_zero_eval]
    norm_num only [Nat.factorial,Nat.cast_one,inv_one,sub_zero,pow_one,smul_eq_mul,one_mul]
    rw [h1,iteratedDeriv_one]
  rw [hformula] at he
  rw [he]
  norm_num only [Nat.factorial,Nat.cast_ofNat,sub_zero,abs_div,abs_mul,abs_pow,
    abs_of_pos hs]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM t ht) (by positivity)) (by norm_num)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma line_linear_remainder {f : E → ℝ} {x v : E} {s M : ℝ} (hs : 0 < s)
    (hf : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 2 f (x+t • v))
    (hM : ∀ t ∈ Ioo 0 s,|iteratedDeriv 2 (fun r : ℝ => f ((x+t • v)+r • v)) 0| ≤ M) :
    |f (x+s • v)-(f x+s*(fderiv ℝ f x v))| ≤ M*s^2/2 := by
  have hline : ContDiff ℝ 2 (fun t : ℝ => x+t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hc : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 2 (fun r : ℝ => f (x+r • v)) t := by
    intro t ht
    exact (hf t ht).comp t hline.contDiffAt
  have h0 := hc 0 (left_mem_Icc.mpr hs.le)
  have hd := deriv_line ((hf 0 (left_mem_Icc.mpr hs.le)).differentiableAt (by norm_num))
  have hb : ∀ t ∈ Ioo 0 s,|iteratedDeriv 2 (fun r : ℝ => f (x+r • v)) t| ≤ M := by
    intro t ht
    simpa only [line_shift_iteratedDeriv] using hM t ht
  have hh := linear_remainder hs (fun t ht => (hc t ht).contDiffWithinAt) h0 hb
  simpa only [hd,zero_smul,add_zero] using hh

end CurrentKS.Difference

end OAI
