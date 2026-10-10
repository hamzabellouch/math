import OAI.Probability.SATComputability.FiniteEnumeration
import OAI.Probability.SATComputability.UpperCertificates

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter RapidForcing.EffectiveArithmetic
open scoped Topology

def lowerProgram (C N s : ℕ) : ℚ :=
  rationalCenter ((N + s + 1)^12) 3 - (C : ℚ) / (s + 1)

attribute [local irreducible] rationalCenter

private theorem sampleCenter_computable (N : ℕ) :
    Computable (fun s : ℕ => rationalCenter ((N + s + 1)^12) 3) := by
  have hi : Computable (fun s : ℕ => (((N + s + 1)^12), (3 : ℕ))) := by fun_prop
  exact Computable.comp (f := fun p : ℕ × ℕ => rationalCenter p.1 p.2)
    (g := fun s : ℕ => (((N + s + 1)^12), (3 : ℕ))) rationalCenter_computable hi

private theorem correction_computable (C : ℕ) :
    Computable (fun s : ℕ => (C : ℚ) / (s + 1)) := by
  have hi : Computable (fun s : ℕ => ((C : ℤ), s + 1)) := by fun_prop
  have h := Computable.comp (f := fun p : ℤ × ℕ => (p.1 : ℚ) / p.2)
    (g := fun s : ℕ => ((C : ℤ), s + 1)) computable_rat_divNat hi
  exact h.of_eq (fun s => by simp)

@[fun_prop] theorem lowerProgram_computable (C N : ℕ) :
    Computable (lowerProgram C N) :=
  computable_rat_sub.comp ((sampleCenter_computable N).pair (correction_computable C))

theorem exists_lowerProgram :
    ∃ lower : ℕ → ℚ, Computable lower ∧
      (∀ i, (lower i : ℝ) ≤ limitingCenter 3) ∧
      (∀ ε : ℝ, 0 < ε → ∃ i, limitingCenter 3 - ε < (lower i : ℝ)) := by
  obtain ⟨C, N, _, _, hbound, hlim⟩ := exists_rational_lower_certificates
  refine ⟨lowerProgram C N, lowerProgram_computable C N, hbound, ?_⟩
  intro ε hε
  exact (hlim.eventually (Ioi_mem_nhds (sub_lt_self _ hε))).exists

theorem threshold_program_of_trial_separation {T : TrialEvaluation}
    (hT : TrialSeparation T (limitingCenter 3)) :
    ∃ (q : ℕ → ℚ) (c : Nat.Partrec.Code),
      Computable q ∧
      (∀ r, c.eval r = Part.some (Encodable.encode (q r))) ∧
      (∀ r, |(q r : ℝ) - limitingCenter 3| ≤ (2 ^ r : ℝ)⁻¹) := by
  obtain ⟨lower, hl, hs, hd⟩ := exists_lowerProgram
  obtain ⟨q, hq, he⟩ := computable_of_trial_separation hT hl hs hd
  obtain ⟨c, hc⟩ := rational_sequence_code hq
  exact ⟨q, c, hq, hc, he⟩

end FixedClauseThreshold.Computability

end OAI
