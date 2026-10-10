import OAI.Combinatorics.ContingencyTables.Dense.DenseBoundedTrial
import OAI.Combinatorics.ContingencyTables.Dense.DenseIdealRejection
import OAI.Combinatorics.ContingencyTables.Transport.RejectionLaw

namespace OAI

/-! # The bounded dense sampler's actual finite output law -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def trialSuccess (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j)
    (t : DenseTrial R P d q) : Option (Table R P) :=
  if ht : TrialAccepted R P d e t then some (trialTable R P d e htotal t ht) else none

omit [DecidableEq I] [DecidableEq J] in
theorem trialSuccess_some_iff (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j)
    (t : DenseTrial R P d q) (X : Table R P) :
    trialSuccess R P d e htotal t = some X ↔ t = tableTrial R P d hd hR hP e X := by
  constructor
  · intro h
    unfold trialSuccess at h
    split_ifs at h with ht
    · have he := Option.some.inj h
      rw [← he, tableTrial_trialTable]
  · rintro rfl
    simp only [trialSuccess, dite_eq_left (tableTrial_accepted R P d hd hR hP e X),
      trialTable_tableTrial]

theorem trialSuccess_ideal_mass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) (X : Table R P) :
    successMass (rationalTrialLaw R P d hd hR hP e) (trialSuccess R P d e htotal) X =
      rationalTableMass R P d hd hR hP e X := by
  unfold successMass
  simp_rw [trialSuccess_some_iff R P d hd hR hP e htotal]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem trialSuccess_ideal_failure (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) :
    failureMass (rationalTrialLaw R P d hd hR hP e) (trialSuccess R P d e htotal) =
      1 - ∑ X, rationalTableMass R P d hd hR hP e X := by
  have h := success_failure_total (rationalTrialLaw R P d hd hR hP e) (trialSuccess R P d e htotal)
  simp_rw [trialSuccess_ideal_mass R P d hd hR hP e htotal] at h
  linarith

def denseBoundedLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) : RationalLaw (Table R P) :=
  retryLaw (boundedTrialLaw R P d hd hR hP hfree e h a)
    (trialSuccess R P d e htotal) fallback (d ^ 4 * (h + 1))

/-- The finite sampler always returns an actual table and is within the
requested error of uniform, assuming finite-box interpolation and finite
Cheeger inequalities. -/
theorem denseBoundedLaw_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) :
    let _ : Nonempty (Table R P) := ⟨fallback⟩
    (variation (denseBoundedLaw R P d hd hR hP hfree e htotal h a fallback)
      (uniformLaw (α := Table R P)) : ℝ) ≤ (2 : ℝ) ^ (-(h : ℝ)) := by
  let : Nonempty (Table R P) := ⟨fallback⟩
  let p := boundedTrialLaw R P d hd hR hP hfree e h a
  let q₀ := rationalTrialLaw R P d hd hR hP e
  let f := trialSuccess R P d e htotal
  let n := d ^ 4 * (h + 1)
  have hg : successMass q₀ f = rationalTableMass R P d hd hR hP e :=
    funext (trialSuccess_ideal_mass R P d hd hR hP e htotal)
  have hf : failureMass q₀ f = 1 - ∑ X, rationalTableMass R P d hd hR hP e X :=
    trialSuccess_ideal_failure R P d hd hR hP e htotal
  have hi : (variation (retryLaw q₀ f fallback n) (uniformLaw (α := Table R P)) : ℝ) ≤
      (63 / 64 : ℝ) ^ n := by
    have hi₀ := dense_ideal_rejection_variation R P d hd hR hP hRmax hPmax hdimR hdimP
      hfree htotal e n fallback
    unfold variation
    change (((∑ X : Table R P,
      |(retryLaw q₀ f fallback n).mass X - uniformMass|) / 2 : ℚ) : ℝ) ≤ _
    simp_rw [retryLaw_mass]
    rw [hg, hf]
    exact hi₀
  have hv := retryLaw_variation p q₀ f fallback n
  have hvc : (variation (retryLaw p f fallback n) (retryLaw q₀ f fallback n) : ℝ) ≤
      (n : ℝ) * (variation p q₀ : ℝ) := by exact_mod_cast hv
  have ht := boundedTrialLaw_variation R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal
    e hPL hCheeger h a
  have hm := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ n by positivity)
  have htri := variation_triangle (retryLaw p f fallback n) (retryLaw q₀ f fallback n)
    (uniformLaw (α := Table R P))
  have htric : (variation (retryLaw p f fallback n) (uniformLaw (α := Table R P)) : ℝ) ≤
      (variation (retryLaw p f fallback n) (retryLaw q₀ f fallback n) : ℝ) +
      (variation (retryLaw q₀ f fallback n) (uniformLaw (α := Table R P)) : ℝ) := by exact_mod_cast htri
  change (variation (retryLaw p f fallback n) (uniformLaw (α := Table R P)) : ℝ) ≤ _
  apply (htric.trans (add_le_add (hvc.trans hm) hi)).trans
  have he : (n : ℝ) * ((1 + (d : ℝ)) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d)))) =
      ((d ^ 4 * (h + 1) * (1 + d) : ℕ) : ℝ) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
    dsimp [n]
    push_cast
    ring
  rw [he, add_comm]
  exact dense_total_error_budget d h hd

end

end ContingencyTables.GridBoundary

end OAI
