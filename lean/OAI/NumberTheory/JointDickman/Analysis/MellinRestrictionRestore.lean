import OAI.NumberTheory.JointDickman.Analysis.MellinRestrictionEnergy

namespace OAI

/-! # Restoring the full polynomial after an arithmetic cutoff -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

theorem angularMellin_energy_of_restriction (E : ℕ → Prop) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 < T)
    {S : Set ℝ} (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤
      2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
        (fun n => if E n then f n else 0) t‖^2)+
      16*Real.exp 1*(T/N+2)*(((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N := by
  classical
  have hs := mrt_restricted_energy_split
    (angularMellinPolynomial (Ioc N (2*N)) f)
    (angularMellinPolynomial (Ioc N (2*N)) (fun n => if E n then f n else 0))
    (angularMellinPolynomial_continuous _ _) (angularMellinPolynomial_continuous _ _) hT.le hS
  have he := angularMellin_restriction_error_energy E f hf hN hT
  simp_rw [angularMellinPolynomial_sub, norm_sub_rev] at he
  calc
    _ ≤ _ := hs
    _ ≤ 2*(8*Real.exp 1*(T/N+2)*
        (((Ioc N (2*N)).filter (fun n => ¬E n)).card:ℝ)/N)+
        2*(∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
          (fun n => if E n then f n else 0) t‖^2) := by gcongr
    _ = _ := by ring

end JointDickman

end OAI
