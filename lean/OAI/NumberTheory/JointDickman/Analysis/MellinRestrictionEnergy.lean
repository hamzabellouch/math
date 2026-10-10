import OAI.NumberTheory.JointDickman.Analysis.TypicalMellinLowFrequency
import OAI.NumberTheory.TwoPointCorrelations.MRTRestrictedEnergy

namespace OAI

/-! # Removing a sparse arithmetic cutoff in full frequency energy -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

theorem angularMellin_restriction_error_energy (E : ℕ → Prop) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
      (fun n => (if E n then f n else 0)-f n) t‖^2) ≤
      8*Real.exp 1*(T/N+2)*(((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N := by
  classical
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hs : (∑ n ∈ Ioc N (2*N),
      ‖((if E n then f n else 0)-f n)/(n:ℂ)‖^2) ≤
      (((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/(N:ℝ)^2 := by
    calc
      _ ≤ ∑ n ∈ Ioc N (2*N), if ¬E n then (1/(N:ℝ))^2 else 0 := by
        apply sum_le_sum
        intro n hn
        have hnr : 0 < (n:ℝ) := by exact_mod_cast hN.trans (mem_Ioc.mp hn).1
        by_cases he : E n
        · simp [he]
        · simp only [he,ite_false,not_false_eq_true,ite_true,zero_sub,norm_div,
            norm_neg,Complex.norm_natCast]
          apply pow_le_pow_left₀ (by positivity)
          exact (div_le_div_of_nonneg_right (hf n) hnr.le).trans
            (one_div_le_one_div_of_le hNr (by exact_mod_cast (mem_Ioc.mp hn).1.le))
      _ = _ := by
        rw [← sum_filter,sum_const,nsmul_eq_mul,div_pow]
        ring
  have hb := mrt_dirichlet_mean_square_subset (Ioc N (2*N)) (N := 2*N) (by
    intro n hn
    exact mem_Ioc.mpr ⟨hN.trans (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2⟩)
    (fun n => ((if E n then f n else 0)-f n)/(n:ℂ)) hT
  change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
    (fun n => (if E n then f n else 0)-f n) t‖^2) ≤ _ at hb
  apply hb.trans
  calc
    _ ≤ 8*Real.exp 1*(T+((2*N:ℕ):ℝ))*
        ((((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by push_cast; field_simp

/-- The cutoff costs its ordinary density, uniformly on every frequency
subset of a fixed polynomial-length interval. -/
theorem angularMellin_restriction_energy (E : ℕ → Prop) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T)
    {S : Set ℝ} (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
      (fun n => if E n then f n else 0) t‖^2) ≤
      2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2)+
        16*Real.exp 1*(T/N+2)*(((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N := by
  classical
  have hs := mrt_restricted_energy_split
    (angularMellinPolynomial (Ioc N (2*N)) (fun n => if E n then f n else 0))
    (angularMellinPolynomial (Ioc N (2*N)) f)
    (angularMellinPolynomial_continuous _ _) (angularMellinPolynomial_continuous _ _) hT.le hS
  simp_rw [← angularMellinPolynomial_sub] at hs
  have he := angularMellin_restriction_error_energy E f hf hN hT
  calc
    _ ≤ _ := hs
    _ ≤ 2*(8*Real.exp 1*(T/N+2)*
        (((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N)+
        2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) := by
      gcongr
    _ = _ := by ring

end JointDickman

end OAI
