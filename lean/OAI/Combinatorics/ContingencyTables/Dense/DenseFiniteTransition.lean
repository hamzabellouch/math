import OAI.Combinatorics.ContingencyTables.Dense.DenseAxisBits
import OAI.Combinatorics.ContingencyTables.Dense.DenseExponentBound
import OAI.Combinatorics.ContingencyTables.Dense.DenseRationalKernel
import OAI.Combinatorics.ContingencyTables.Transport.FiniteMetropolis

namespace OAI

/-! # The bounded finite fair-bit experiment implements the dense transition -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CommonBasesFPRAS

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def finiteDenseStepLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) :=
  finiteAcceptLaw a
    (fun z : Fin (2 ^ Nat.clog 2 (8 * d)) => axisCodeStep a z)
    (fun b => FairBits.acceptDyadic
      (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))

/-- A proposal integer followed by the fixed acceptance allowance realizes
the entire dense transition law, including unused codes and rejected moves. -/
theorem finiteDenseStepLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    finiteDenseStepLaw R P d e a = rationalTransitionLaw R P d hd hfree e a := by
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  apply RationalLaw.eq_of_off_diagonal _ _ a
  intro b hba
  apply Rat.cast_injective (α := ℝ)
  change ((finiteAcceptLaw a
    (fun z : Fin (2 ^ Nat.clog 2 (8 * d)) => axisCodeStep a z)
    (fun b => FairBits.acceptDyadic
      (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))).mass b : ℝ) =
      (rationalTransition R P d e a b : ℝ)
  rw [finiteAcceptLaw_off_diagonal a b _ _ hba.symm,
    axisCodeStep_count (dense_proposal_code_bound d q hq)]
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat]
  push_cast
  rw [Finset.filter_congr_decidable (Finset.univ : Finset (Fin (2 ^ (8 * d ^ 5))))
    (FairBits.acceptDyadic (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))
    (fun z => Classical.propDecidable _)]
  rw [denseMetropolis_finite_coin R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e a b]
  unfold rationalTransition
  rw [ite_eq_right hba.symm, add_zero, rationalMove_cast]
  unfold MetropolisChain.move binProposal
  by_cases hab : Neighbor a b <;> simp [hab]

end

end ContingencyTables.GridBoundary

end OAI
