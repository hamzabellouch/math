import OAI.Combinatorics.ContingencyTables.Dense.DenseFiniteTransition
import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits

namespace OAI

/-! # A fixed Boolean word realizes each exact dense transition -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseStepBits (d : ℕ) : ℕ := Nat.clog 2 (8 * d) + 8 * d ^ 5

def denseBitStep (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8))
    (bits : Fin (denseStepBits d) → Bool) : Grid (I := Fin q) (4 * d ^ 8) :=
  let z := pairWordEquiv (Nat.clog 2 (8 * d)) (8 * d ^ 5) bits
  match axisCodeStep a z.1 with
  | none => a
  | some b => if z.2.val < 2 ^ (8 * d ^ 5 - (denseExponent R P d e b - denseExponent R P d e a))
      then b else a

def denseBitStepLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    RationalLaw (Grid (I := Fin q) (4 * d ^ 8)) :=
  mapLaw (uniformLaw (α := Fin (denseStepBits d) → Bool)) (denseBitStep R P d e a)

omit [DecidableEq I] [DecidableEq J] in
theorem denseBitStepLaw_eq_finite (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    denseBitStepLaw R P d e a = finiteDenseStepLaw R P d e a := by
  let E := pairWordEquiv (Nat.clog 2 (8 * d)) (8 * d ^ 5)
  let f := finiteAcceptStep a
    (fun z : Fin (2 ^ Nat.clog 2 (8 * d)) => axisCodeStep a z)
    (fun b => FairBits.acceptDyadic
      (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))
  have hf : denseBitStep R P d e a = fun bits => f (E bits) := by
    funext bits
    dsimp [denseBitStep, f, E, finiteAcceptStep]
    simp only [FairBits.acceptDyadic]
    cases axisCodeStep a ((pairWordEquiv (Nat.clog 2 (8 * d)) (8 * d ^ 5)) bits).1 with
    | none => rfl
    | some b => dsimp only; split_ifs <;> rfl
  unfold denseBitStepLaw
  rw [hf]
  change mapLaw (uniformLaw (α := Fin (Nat.clog 2 (8 * d) + 8 * d ^ 5) → Bool))
    (fun bits => f (E bits)) = _
  rw [← map_equiv E, uniform_equiv]
  rw [← uniform_product]
  rfl

/-- The declared q_bin+8d^5 independent unbiased bits implement exactly
the transition law whose mixing bound was proved. -/
theorem denseBitStepLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    denseBitStepLaw R P d e a = rationalTransitionLaw R P d hd hfree e a := by
  rw [denseBitStepLaw_eq_finite]
  exact finiteDenseStepLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e a

end

end ContingencyTables.GridBoundary

end OAI
