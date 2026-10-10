import OAI.Combinatorics.ContingencyTables.Dense.DenseRational
import OAI.Combinatorics.ContingencyTables.Transport.FirstSuccess

namespace OAI

/-! # The rational ideal dense rejection law -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def rationalBinWeight (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) : ℚ :=
  1 / (2 : ℚ) ^ denseExponent R P d e a

theorem rationalBinWeight_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    (rationalBinWeight R P d e a : ℝ) = denseBinWeight R P d e a := by
  rw [denseBinWeight_eq_dyadic]
  simp only [rationalBinWeight, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]

def rationalTrialMass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) : ℚ :=
  rationalBinWeight R P d e t.1 /
    (∑ a : Grid (I := Fin q) (4 * d ^ 8), rationalBinWeight R P d e a) /
      Fintype.card (Offset (integerWidth R P d))

theorem rationalTrialMass_cast (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) :
    (rationalTrialMass R P d e t : ℝ) = denseTrialMass R P d e t := by
  simp only [rationalTrialMass, denseTrialMass, Rat.cast_div, Rat.cast_sum,
    Rat.cast_natCast, rationalBinWeight_cast]

def rationalTrialLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) : RationalLaw (DenseTrial R P d q) where
  mass := rationalTrialMass R P d e
  nonnegative := fun t => by
    have h := (denseTrialMass_pos R P d hd hR hP e t).le
    rw [← rationalTrialMass_cast] at h
    exact_mod_cast h
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum, rationalTrialMass_cast, Rat.cast_one]
    exact denseTrialMass_sum R P d hd hR hP e

def rationalTableMass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (X : Table R P) : ℚ :=
  rationalTrialMass R P d e (tableTrial R P d hd hR hP e X)

theorem rationalTableMass_total (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) :
    ((∑ X : Table R P, rationalTableMass R P d hd hR hP e X) : ℝ) =
      denseAcceptanceMass R P d e := by
  rw [denseAcceptanceMass, ← Finset.sum_filter]
  have hs : (∑ t : {t : DenseTrial R P d q // TrialAccepted R P d e t},
      denseTrialMass R P d e t.val) =
      ∑ t ∈ Finset.univ.filter (TrialAccepted R P d e), denseTrialMass R P d e t := by
    exact (Finset.sum_subtype (p := TrialAccepted R P d e)
      (Finset.univ.filter (TrialAccepted R P d e)) (fun _ => by simp)
      (denseTrialMass R P d e)).symm
  rw [← hs]
  symm
  apply Fintype.sum_equiv (acceptedTrialEquiv R P d hd hR hP e htotal)
  intro t
  simp only [rationalTableMass, rationalTrialMass_cast]
  congr 1
  exact (tableTrial_trialTable R P d hd hR hP e htotal t.val t.property).symm

theorem rationalTableMass_uniform (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q) (X : Table R P) :
    rationalTableMass R P d hd hR hP e X /
      (∑ Y : Table R P, rationalTableMass R P d hd hR hP e Y) =
        1 / Fintype.card (Table R P) := by
  apply Rat.cast_injective (α := ℝ)
  simp only [Rat.cast_div, Rat.cast_sum, Rat.cast_one, Rat.cast_natCast,
    rationalTableMass, rationalTrialMass_cast]
  exact denseTrial_conditional_uniform R P d hd hR hP hRmax hPmax hfree e X

end

end ContingencyTables.GridBoundary

end OAI
