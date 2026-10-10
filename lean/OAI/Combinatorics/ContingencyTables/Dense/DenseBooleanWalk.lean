import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanStep
import OAI.Combinatorics.ContingencyTables.Dense.DenseFiniteWalk
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk

namespace OAI

/-! # The dense bin draw as one bounded unbiased Boolean word -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

def gridWordEquiv (n k : ℕ) : (Fin (n * k) → Bool) ≃ (Fin n → Fin k → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseBooleanWalk (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ)
    (bits : Fin (n * denseStepBits d) → Bool) : Grid (I := Fin q) (4 * d ^ 8) :=
  wordWalk (denseBitStep R P d e) a n (gridWordEquiv n (denseStepBits d) bits)

def denseBooleanWalkLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ) :
    RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) :=
  mapLaw (uniformLaw (α := Fin (n * denseStepBits d) → Bool)) (denseBooleanWalk R P d e a n)

/-- Exactly n*(q_bin+8d^5) unbiased bits give the rational n-step law. -/
theorem denseBooleanWalkLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ) :
    denseBooleanWalkLaw R P d e a n = rationalWalkLaw R P d hd hfree e n a := by
  have hk : (fun s => mapLaw (uniformLaw (α := Fin (denseStepBits d) → Bool)) (denseBitStep R P d e s)) =
      finiteDenseStepLaw R P d e := funext (denseBitStepLaw_eq_finite R P d e)
  unfold denseBooleanWalkLaw denseBooleanWalk
  rw [← map_equiv (gridWordEquiv n (denseStepBits d)), uniform_equiv]
  change wordWalkLaw (denseBitStep R P d e) a n = _
  rw [wordWalkLaw_eq, hk]
  exact finiteDenseWalkLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e a n

end

end ContingencyTables.GridBoundary

end OAI
