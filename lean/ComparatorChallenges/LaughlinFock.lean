import Mathlib

namespace OAI

/-! The spherical V₁ Hamiltonian inequality on the full fermionic Fock space. -/

noncomputable section

namespace Laughlin

noncomputable def pairCoefficient (Q p : ℕ) (x y : Fin (Q+1)) : ℝ :=
  if x.val + y.val = p+1 then
    ((x.val : ℝ) - (y.val : ℝ)) *
      Real.sqrt (((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) *
        (p.factorial : ℝ)) /
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) *
          (x.val.factorial : ℝ) * (y.val.factorial : ℝ))) / Real.sqrt 2
  else 0

end Laughlin

run_cmd Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace LaughlinFock

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

abbrev Orbital (Q : ℕ) := Fin (Q + 1)
abbrev Occupation (Q : ℕ) := Finset (Orbital Q)
abbrev FockMatrix (Q : ℕ) := Matrix (Occupation Q) (Occupation Q) ℂ

def tensorPairCoefficient (Q p : ℕ) (i j : Orbital Q) : ℝ :=
  _root_.OAI.Laughlin.pairCoefficient Q p i j

def pairCoefficient (Q p : ℕ) (i j : Orbital Q) : ℝ :=
  Real.sqrt 2 * tensorPairCoefficient Q p i j

def annihilator (Q : ℕ) (j : Orbital Q) : FockMatrix Q := fun A B =>
  if j ∈ B ∧ A = B.erase j then
    (-1 : ℂ) ^ (B.filter (fun i => i < j)).card
  else 0

def pairAnnihilator (Q p : ℕ) : FockMatrix Q :=
  ∑ i : Orbital Q, ∑ j : Orbital Q,
    if i < j then
      (pairCoefficient Q p i j : ℂ) • (annihilator Q j * annihilator Q i)
    else 0

def hamiltonian (Q : ℕ) : FockMatrix Q :=
  ∑ p ∈ Finset.range (2 * Q - 1),
    (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p

def gammaStar : ℝ := 4616733319001 / 10 ^ 14

def FockInequality (Q : ℕ) (γ : ℝ) : Prop :=
  (hamiltonian Q * hamiltonian Q - γ • hamiltonian Q).PosSemidef

theorem thm_fock (γ : ℝ) (hγ : 0 < γ) (hγStar : γ < gammaStar) :
    ∃ Qγ : ℤ, 1 ≤ Qγ ∧ ∀ Q : ℤ, Qγ ≤ Q → FockInequality Q.toNat γ := by
  sorry

end LaughlinFock

end

end OAI
