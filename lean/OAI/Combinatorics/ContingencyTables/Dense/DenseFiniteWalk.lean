import OAI.Combinatorics.ContingencyTables.Dense.DenseFiniteTransition
import OAI.Combinatorics.ContingencyTables.Transport.RationalWalks

namespace OAI

/-! # Independent bounded dense transitions realize the mixed bin law -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def finiteDenseWalkLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ) :
    RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) :=
  walkLaw (finiteDenseStepLaw R P d e) a n

theorem finiteDenseWalkLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) (n : ℕ) :
    finiteDenseWalkLaw R P d e a n = rationalWalkLaw R P d hd hfree e n a := by
  induction n with
  | zero =>
    apply RationalLaw.ext
    funext b
    change (if b = a then (1 : ℚ) else 0) = if a = b then 1 else 0
    simp [eq_comm]
  | succ n ih =>
    apply RationalLaw.ext
    funext b
    change (∑ c, (finiteDenseWalkLaw R P d e a n).mass c * (finiteDenseStepLaw R P d e c).mass b) =
      ∑ c, rationalWalk R P d e n a c * rationalTransition R P d e c b
    rw [ih]
    apply Finset.sum_congr rfl
    intro c _
    rw [finiteDenseStepLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e c]
    rfl

end

end ContingencyTables.GridBoundary

end OAI
