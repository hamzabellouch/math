import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteCompositionGrowth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! Fixed-order spatial jet estimates for the actual exterior vector field. -/

open Set
open scoped ContDiff
namespace DefocusingNLS

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem spectralRemote_linear_jet (A : E →L[ℝ] F) (x : E) (k : ℕ)
    (M : ℝ) (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) (hx : ‖A x‖ ≤ M) :
    ‖iteratedFDeriv ℝ k A x‖ ≤ M := by
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hx
  | succ k =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (A : E → F) = fun _ => A := by
      funext y
      exact A.hasFDerivAt.fderiv
    rw [he]
    cases k with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hA
    | succ k => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero] using hM

theorem spectralRemote_right_jet (A : E →L[ℝ] F) (hA : ‖A‖ ≤ 1)
    (f : F → G) (hf : ContDiff ℝ ∞ f) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ A) x‖ ≤ ‖iteratedFDeriv ℝ k f (A x)‖ := by
  rw [A.iteratedFDeriv_comp_right hf x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏ _i : Fin k, ‖A‖) ≤ 1 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg A) hA
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)

theorem spectralRemote_time_exp_jet (x : ℝ × E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ × E => Real.exp (2*y.1)) x‖ ≤
      2^k*Real.exp (2*x.1) := by
  have h := spectralRemote_right_jet (ContinuousLinearMap.fst ℝ ℝ E)
    (ContinuousLinearMap.norm_fst_le ..) (fun t : ℝ => Real.exp (2*t))
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)) x k
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_exp_const_mul] at h
  simpa only [ContinuousLinearMap.coe_fst',Function.comp_def,Real.norm_eq_abs,abs_mul,abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),abs_of_pos (Real.exp_pos _)] using h

theorem spectralRemote_state_linear_jet (A : E →L[ℝ] F) (x : ℝ × E)
    (M : ℝ) (hM : 1 ≤ M) (hx : ‖x.2‖ ≤ M) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ × E => A y.2) x‖ ≤ ‖A‖*M := by
  let T := A.comp (ContinuousLinearMap.snd ℝ ℝ E)
  apply spectralRemote_linear_jet T x k (‖A‖*M) (by positivity)
  · exact (A.opNorm_comp_le (ContinuousLinearMap.snd ℝ ℝ E)).trans ((mul_le_of_le_one_right (norm_nonneg A)
      (ContinuousLinearMap.norm_snd_le ..)).trans
      (le_mul_of_one_le_right (norm_nonneg A) hM))
  · exact (A.le_opNorm x.2).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg A))

theorem spectralRemote_time_linear_jet (A : E →L[ℝ] F) (x : ℝ × E)
    (M : ℝ) (hM : 1 ≤ M) (hx : ‖x.2‖ ≤ M) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ × E => Real.exp (2*y.1) • A y.2) x‖ ≤
      ((∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*2^i)*‖A‖*M)*Real.exp (2*x.1) := by
  have he : ContDiff ℝ ∞ (fun y : ℝ × E => Real.exp (2*y.1)) := by fun_prop
  have ha : ContDiff ℝ ∞ (fun y : ℝ × E => A y.2) := A.contDiff.comp contDiff_snd
  apply (norm_iteratedFDeriv_smul_le he ha x (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1),
        ((k.choose i : ℝ)*2^i*‖A‖*M)*Real.exp (2*x.1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hb := mul_le_mul (spectralRemote_time_exp_jet x i)
        (spectralRemote_state_linear_jet A x M hM hx (k-i))
        (norm_nonneg _) (by positivity)
      have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (k.choose i) : (0 : ℝ) ≤ _)
      convert hh using 1 <;> ring
    _ = _ := by simp only [Finset.sum_mul]

end DefocusingNLS

end OAI
