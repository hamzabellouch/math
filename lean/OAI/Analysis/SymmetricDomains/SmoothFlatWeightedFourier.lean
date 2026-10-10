import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061

lemma weighted_summable_of_cubic_decay {a : ℤ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : ℤ, n ≠ 0 → ‖a n‖ ≤ C/|((n : ℤ) : ℝ)|^3) :
    Summable (fun n : ℤ => (1+|((n : ℤ) : ℝ)|)*‖a n‖) := by
  have hs : Summable (fun n : ℤ => 2*C*(1/(n : ℝ)^2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (2*C)
  have hif : Summable (fun n : ℤ => if n = 0 then 0 else (1+|(n : ℝ)|)*‖a n‖) := by
    apply hs.of_norm_bounded
    intro n
    split_ifs with hn
    · simp [hn]
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |n| from Int.one_le_abs hn)
    have hn0 : 0 < |(n : ℝ)| := lt_of_lt_of_le zero_lt_one hn1
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    calc
      _ ≤ (1+|(n : ℝ)|)*(C/|(n : ℝ)|^3) :=
        mul_le_mul_of_nonneg_left (ha n hn) (by positivity)
      _ ≤ (2*|(n : ℝ)|)*(C/|(n : ℝ)|^3) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 2*C*(1/(n : ℝ)^2) := by
        rw [← sq_abs]
        field_simp
  apply hif.congr_cofinite
  filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton (0 : ℤ))] with n hn
  simp only [Set.mem_compl_iff,Set.mem_singleton_iff] at hn
  simp [hn]

lemma fourierCoeffOn_norm_le {f : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C) (n : ℤ) :
    ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n‖ ≤ C := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero,div_one,one_smul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := C) (f := fun x => fourier (-n) (x : AddCircle (1-0 : ℝ)) • f x) (by
      intro x hx
      rw [norm_smul,fourier_apply,Circle.norm_coe,one_mul]
      exact hf x (by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc hx))
  simpa using h

lemma fourierCoeffOn_deriv_norm_le {f g : ℝ → ℂ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hg : Continuous g) (he : f 0 = f 1) {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n‖ ≤
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) g n‖ / |(n : ℝ)| := by
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num : (0 : ℝ) < 1) hn
    (by simpa only [uIcc_of_le zero_le_one] using hf) (hg.intervalIntegrable 0 1)]
  simp only [he,sub_self,mul_zero,Complex.ofReal_one,Complex.ofReal_zero,sub_zero,one_mul,zero_sub,norm_mul,norm_div]
  simp only [norm_one,norm_neg,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one,Complex.norm_intCast]
  have hpos : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hh : 1/(2*Real.pi*|(n : ℝ)|) ≤ 1/|(n : ℝ)| :=
    one_div_le_one_div_of_le hpos (by nlinarith)
  exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (by ring)

theorem smooth_flat_weighted_fourier {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (h0 : f =ᶠ[𝓝 (0 : ℝ)] 0) (h1 : f =ᶠ[𝓝 (1 : ℝ)] 0) :
    Summable (fun n : ℤ => (1+|(n : ℝ)|)*
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n‖) := by
  have hc (j : ℕ) : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
  have hd (j : ℕ) (x : ℝ) : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j+1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv j (by exact_mod_cast (show (j : ℕ∞) < ⊤ from ENat.natCast_lt_top j)) x).hasDerivAt
  have he (j : ℕ) : iteratedDeriv j f 0 = iteratedDeriv j f 1 := by
    rw [h0.iteratedDeriv_eq j,h1.iteratedDeriv_eq j]
    simp
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 3).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl,zero_le_one⟩)
  apply weighted_summable_of_cubic_decay hC0
  intro n hn
  have hn0 : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hrec (j : ℕ) : ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (iteratedDeriv j f) n‖ ≤
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (iteratedDeriv (j+1) f) n‖ / |(n : ℝ)| :=
    fourierCoeffOn_deriv_norm_le (fun x _ => hd j x) (hc (j+1)) (he j) hn
  have h3 := fourierCoeffOn_norm_le hC n
  have h2 := (hrec 2).trans (div_le_div_of_nonneg_right h3 hn0.le)
  have h1' := (hrec 1).trans (div_le_div_of_nonneg_right h2 hn0.le)
  have h0' := (hrec 0).trans (div_le_div_of_nonneg_right h1' hn0.le)
  simpa only [iteratedDeriv_zero,div_div,pow_succ,pow_zero,one_mul] using h0'

end Release061

end

end OAI
