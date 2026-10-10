import Mathlib

namespace OAI

namespace Laughlin
open scoped BigOperators

abbrev Configuration (N Q : ℕ) := Fin N → Fin (Q+1)
abbrev State (N Q : ℕ) := Configuration N Q → ℂ

def Antisymmetric {N Q : ℕ} (ψ : State N Q) : Prop :=
  ∀ (i j : Fin N), i ≠ j → ∀ a, ψ (a ∘ Equiv.swap i j) = -ψ a

noncomputable def pairCoefficient (Q p : ℕ) (x y : Fin (Q+1)) : ℝ :=
  if x.val + y.val = p+1 then
    ((x.val : ℝ) - (y.val : ℝ)) *
      Real.sqrt (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) *
        (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) / Real.sqrt 2
  else 0

noncomputable def pairAmplitude {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (p : ℕ) (a : Configuration N Q) : ℂ :=
  ∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
    (pairCoefficient Q p x y : ℂ) * ψ (Function.update (Function.update a i x) j y)

noncomputable def energy {N Q : ℕ} (ψ : State N Q) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then
    ∑ p ∈ Finset.range (2*Q-1), ∑ a : Configuration N Q,
      if a i = 0 ∧ a j = 0 then ‖pairAmplitude ψ i j p a‖ ^ 2 else 0
  else 0

abbrev SpinorVariables (N : ℕ) := Fin N × Bool

noncomputable def bracket {N : ℕ} (i j : Fin N) : MvPolynomial (SpinorVariables N) ℂ :=
  MvPolynomial.X (i,false) * MvPolynomial.X (j,true) -
    MvPolynomial.X (j,false) * MvPolynomial.X (i,true)

noncomputable def laughlinPolynomial (N : ℕ) : MvPolynomial (SpinorVariables N) ℂ :=
  ∏ i : Fin N, ∏ j : Fin N, if i < j then bracket i j ^ 3 else 1

noncomputable def monomialExponent {N Q : ℕ} (a : Configuration N Q) : SpinorVariables N →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun ib => if ib.2 then (a ib.1).val else Q - (a ib.1).val)
    (by intro; simp)

noncomputable def laughlinVector (N Q : ℕ) : State N Q := fun a =>
  (laughlinPolynomial N).coeff (monomialExponent a) /
    ((∏ i : Fin N, Real.sqrt (Nat.choose Q (a i).val : ℝ) : ℝ) : ℂ)

noncomputable def distanceToLaughlinSq {N Q : ℕ} (ψ : State N Q) : ℝ :=
  sInf (Set.range (fun c : ℂ => ∑ a : Configuration N Q,
    ‖ψ a - c * laughlinVector N Q a‖ ^ 2))

def MainTarget : Prop :=
  ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ ψ : State N (3*(N-1)), Antisymmetric ψ →
      (1/100 : ℝ) * distanceToLaughlinSq ψ ≤ energy ψ

theorem mainTarget_proved : MainTarget := by
  sorry

end Laughlin

end OAI
