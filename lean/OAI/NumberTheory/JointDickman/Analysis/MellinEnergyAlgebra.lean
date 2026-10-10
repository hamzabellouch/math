import OAI.NumberTheory.JointDickman.Analysis.MellinRestrictionEnergy

namespace OAI

/-! # Centering and splitting the actual angular-frequency integrals -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations

lemma angularMellinPolynomial_const_mul (K : Finset ℕ) (f : ℕ → ℂ) (c : ℂ) (t : ℝ) :
    angularMellinPolynomial K (fun n => c*f n) t = c*angularMellinPolynomial K f t := by
  simp only [angularMellinPolynomial,mul_div_assoc,mul_assoc,mul_sum]

lemma angularMellin_centered_energy (K : Finset ℕ) (f g : ℕ → ℂ) {c : ℂ}
    (hc : ‖c‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T) {S : Set ℝ}
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial K (fun n => f n-c*g n) t‖^2) ≤
      2*(∫ t in S, ‖angularMellinPolynomial K f t‖^2)+
      2*(∫ t in S, ‖angularMellinPolynomial K g t‖^2) := by
  have hi (a : ℕ → ℂ) := mrt_continuous_square_integrable
    (angularMellinPolynomial_continuous K a) hT hS
  calc
    _ ≤ ∫ t in S, (2*‖angularMellinPolynomial K f t‖^2+
        2*‖angularMellinPolynomial K g t‖^2) := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        (((hi f).const_mul 2).add ((hi g).const_mul 2))
      intro t _
      rw [angularMellinPolynomial_sub,angularMellinPolynomial_const_mul]
      have hn := norm_sub_le (angularMellinPolynomial K f t) (c*angularMellinPolynomial K g t)
      have hm : ‖c*angularMellinPolynomial K g t‖ ≤ ‖angularMellinPolynomial K g t‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hc
      change ‖angularMellinPolynomial K f t-c*angularMellinPolynomial K g t‖^2 ≤
        2*‖angularMellinPolynomial K f t‖^2+2*‖angularMellinPolynomial K g t‖^2
      nlinarith [norm_nonneg (angularMellinPolynomial K f t),
        norm_nonneg (angularMellinPolynomial K g t),
        norm_nonneg (angularMellinPolynomial K f t-c*angularMellinPolynomial K g t),
        sq_nonneg (‖angularMellinPolynomial K f t‖-‖angularMellinPolynomial K g t‖)]
    _ = _ := by
      rw [integral_add ((hi f).const_mul 2) ((hi g).const_mul 2),
        integral_const_mul,integral_const_mul]

lemma angularMellin_frequency_split (K : Finset ℕ) (f : ℕ → ℂ)
    {T U : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) :
    (∫ t in -T..T, ‖angularMellinPolynomial K f t‖^2) ≤
      (∫ t in -U..U, ‖angularMellinPolynomial K f t‖^2)+
      (∫ t in Set.Ioc (-T) T \ Set.Ioc (-U) U, ‖angularMellinPolynomial K f t‖^2) := by
  have hi := mrt_continuous_square_integrable
    (angularMellinPolynomial_continuous K f) hT (Set.Subset.refl (Set.Ioc (-T) T))
  have he := integral_inter_add_sdiff measurableSet_Ioc hi (t:=Set.Ioc (-U) U)
  have hb := mrt_restricted_square_le_interval (angularMellinPolynomial_continuous K f)
    hU (Set.inter_subset_right : Set.Ioc (-T) T ∩ Set.Ioc (-U) U ⊆ Set.Ioc (-U) U)
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  rw [←he]
  exact add_le_add hb le_rfl

end JointDickman

end OAI
