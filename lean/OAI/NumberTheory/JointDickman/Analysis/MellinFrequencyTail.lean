import OAI.NumberTheory.JointDickman.Analysis.MellinRestrictionEnergy

namespace OAI

/-! # Completing a spectral bound beyond the arithmetic frequency range -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations

lemma angularMellin_dyadic_mean_square (f : ℕ → ℂ) {C : ℝ}
    (_hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) {N : ℕ} (hN : 0 < N)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤
      16*Real.exp 1*C^2*(T/N+1) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hs : (∑ n ∈ Ioc N (2*N), ‖f n/(n:ℂ)‖^2) ≤ C^2/(N:ℝ) := by
    calc
      _ ≤ ∑ n ∈ Ioc N (2*N), C^2*((n:ℝ)^2)⁻¹ := by
        apply sum_le_sum
        intro n hmem
        have hnr : (0:ℝ)<n := by exact_mod_cast hN.trans (mem_Ioc.mp hmem).1
        rw [norm_div,Complex.norm_natCast,div_pow]
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hf n) 2) (by positivity)
      _ = C^2*(∑ n ∈ Ioc N (2*N), ((n:ℝ)^2)⁻¹) := (mul_sum _ _ _).symm
      _ ≤ C^2*((N:ℝ)⁻¹-((2*N:ℕ):ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (α:=ℝ) hN.ne' (by omega)) (sq_nonneg _)
      _ ≤ C^2/(N:ℝ) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (sq_nonneg _)
  have hb := mrt_dirichlet_mean_square_subset (Ioc N (2*N)) (N:=2*N) (by
    intro n hn'
    exact mem_Ioc.mpr ⟨hN.trans (mem_Ioc.mp hn').1,(mem_Ioc.mp hn').2⟩)
    (fun n => f n/(n:ℂ)) hT
  change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤ _ at hb
  calc
    _ ≤ 8*Real.exp 1*(T+((2*N:ℕ):ℝ))*(C^2/N) :=
      hb.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = 8*Real.exp 1*C^2*(T/N+2) := by push_cast; field_simp
    _ ≤ _ := by
      have hd : 0 ≤ T/(N:ℝ) := by positivity
      nlinarith only [mul_nonneg (show 0 ≤ Real.exp 1*C^2 by positivity) hd]

lemma angularMellin_extend_affine (f : ℕ → ℂ) {C A B : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {N : ℕ} (hN : 0 < N)
    (hb : ∀ T : ℝ, 1 ≤ T → T ≤ N →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤ A+B*T/N) :
    ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤
        A+(B+32*Real.exp 1*C^2)*T/N := by
  intro T hT
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  by_cases hTN : T ≤ N
  · apply (hb T hT hTN).trans
    have hpos : 0 ≤ 32*Real.exp 1*C^2*T/N := by positivity
    linear_combination hpos
  · have ht : (N:ℝ)<T := lt_of_not_ge hTN
    have hratio : 1 ≤ T/(N:ℝ) := (le_div_iff₀ hn).mpr (by simpa using ht.le)
    have he := angularMellin_dyadic_mean_square f hC hf hN (by linarith : 0<T)
    have hc := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 16*Real.exp 1*C^2 by positivity)
    have hbt : 0 ≤ B*T/N := by positivity
    linear_combination he + hc + hbt + hA

end JointDickman

end OAI
