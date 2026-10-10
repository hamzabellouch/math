import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanWalk
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanOffsets

namespace OAI

/-! # The full dense trial as one bounded unbiased Boolean word -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

def dependentWordEquiv {q : ℕ} (k : Fin q → ℕ) :
    (Fin (∑ j, k j) → Bool) ≃ (∀ j, Fin (k j) → Bool) :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.piCurry (fun _ _ => Bool))

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseTrialBits (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (h : ℕ) : ℕ :=
  (d ^ 50 * (h + 1) ^ 2) * denseStepBits d +
    ∑ j : Fin q, offsetBitLength (integerWidth R P d (e.symm j)) h d

def trialWordEquiv (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (h : ℕ) : (Fin (denseTrialBits R P d e h) → Bool) ≃
    ((Fin ((d ^ 50 * (h + 1) ^ 2) * denseStepBits d) → Bool) ×
      OffsetWords e (integerWidth R P d) h d) :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
    (dependentWordEquiv (fun j => offsetBitLength (integerWidth R P d (e.symm j)) h d)))

def denseBooleanTrial (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8))
    (bits : Fin (denseTrialBits R P d e h) → Bool) : DenseTrial R P d q :=
  let z := trialWordEquiv R P d e h bits
  (denseBooleanWalk R P d e a (d ^ 50 * (h + 1) ^ 2) z.1,
    drawOffsetWords e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d z.2)

/-- This is the exact law of the full declared Boolean trial, including
all independent quotient offsets, before its integer acceptance test. -/
theorem denseBooleanTrialLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    mapLaw (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
      (denseBooleanTrial R P d hd hR hP e h a) = boundedTrialLaw R P d hd hR hP hfree e h a := by
  unfold denseBooleanTrial
  rw [← map_equiv (trialWordEquiv R P d e h)
    (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
    (fun z => (denseBooleanWalk R P d e a (d ^ 50 * (h+1)^2) z.1,
      drawOffsetWords e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d z.2)),
    uniform_equiv, ← uniform_product, mapLaw_product]
  rw [show mapLaw (uniformLaw (α := Fin ((d ^ 50 * (h + 1) ^ 2) * denseStepBits d) → Bool))
      (denseBooleanWalk R P d e a (d ^ 50 * (h + 1) ^ 2)) =
      rationalWalkLaw R P d hd hfree e (d ^ 50 * (h + 1) ^ 2) a from
    denseBooleanWalkLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e a _]
  unfold boundedTrialLaw
  congr 1
  exact drawOffsetWordsLaw_eq e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d

end

end ContingencyTables.GridBoundary

end OAI
