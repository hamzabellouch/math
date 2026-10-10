import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanTrial
import OAI.Combinatorics.ContingencyTables.Dense.DenseBoundedRejection
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordRejection
import OAI.Combinatorics.ContingencyTables.Dense.DenseBitBudget

namespace OAI

/-! # A bounded unbiased Boolean-word dense table draw -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseDrawBits (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (h : ℕ) : ℕ :=
  (d ^ 4 * (h + 1)) * denseTrialBits R P d e h

def denseBooleanDraw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P)
    (bits : Fin (denseDrawBits R P d e h) → Bool) : Table R P :=
  wordRetry (fun word => trialSuccess R P d e htotal (denseBooleanTrial R P d hd hR hP e h a word))
    fallback (d ^ 4 * (h + 1)) (gridWordEquiv (d ^ 4 * (h + 1)) (denseTrialBits R P d e h) bits)

def denseBooleanDrawLaw (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) : RationalLaw (Table R P) :=
  mapLaw (uniformLaw (α := Fin (denseDrawBits R P d e h) → Bool))
    (denseBooleanDraw R P d hd hR hP e htotal h a fallback)

theorem denseBooleanDrawLaw_eq (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) :
    denseBooleanDrawLaw R P d hd hR hP e htotal h a fallback =
      denseBoundedLaw R P d hd hR hP hfree e htotal h a fallback := by
  unfold denseBooleanDrawLaw denseBooleanDraw
  change mapLaw (uniformLaw (α := Fin ((d^4*(h+1))*denseTrialBits R P d e h) → Bool))
    (fun bits => wordRetry
      (fun word => trialSuccess R P d e htotal (denseBooleanTrial R P d hd hR hP e h a word))
      fallback (d^4*(h+1)) (gridWordEquiv (d^4*(h+1)) (denseTrialBits R P d e h) bits)) = _
  rw [← map_equiv (gridWordEquiv (d ^ 4 * (h + 1)) (denseTrialBits R P d e h)), uniform_equiv]
  change wordRetryLaw
    (fun word => trialSuccess R P d e htotal (denseBooleanTrial R P d hd hR hP e h a word))
    fallback (d ^ 4 * (h + 1)) = _
  rw [wordRetryLaw_eq, ← retryLaw_map,
    denseBooleanTrialLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e h a]
  rfl

/-- The actual finite Boolean draw always has codomain the feasible tables
and its law satisfies the desired dense approximation guarantee. -/
theorem denseBooleanDraw_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4 * d ^ 8)))
    (h : ℕ) (a : Grid (I := Fin q) (4 * d ^ 8)) (fallback : Table R P) :
    let _ : Nonempty (Table R P) := ⟨fallback⟩
    (variation (denseBooleanDrawLaw R P d hd hR hP e htotal h a fallback)
      (uniformLaw (α := Table R P)) : ℝ) ≤ (2 : ℝ) ^ (-(h : ℝ)) := by
  let : Nonempty (Table R P) := ⟨fallback⟩
  rw [denseBooleanDrawLaw_eq R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e h a fallback]
  exact denseBoundedLaw_variation R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal
    e hPL hCheeger h a fallback

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- The full Boolean source has polynomial length in the declared dense
parameters. -/
theorem denseDrawBits_polynomial (R : Option I → ℕ) (P : Option J → ℕ)
    (d C b h : ℕ) (e : I × J ≃ Fin q) (hq : q ≤ d)
    (hwidth : ∀ p, integerWidth R P d p ≤ C) (hb : Nat.clog 2 (C + 2) ≤ b) :
    denseDrawBits R P d e h ≤ 25 * (d + b + h + 1) ^ 62 := by
  have hoff : (∑ j : Fin q, offsetBitLength (integerWidth R P d (e.symm j)) h d) ≤
      d * (b + 1 + 4 * (h + d)) := by
    calc
      _ ≤ ∑ _j : Fin q, (b + 1 + 4 * (h + d)) :=
        Finset.sum_le_sum (fun j _ => denseOffsetBits_upper _ C b h d (hwidth _) hb)
      _ = q * (b + 1 + 4 * (h + d)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hq
  apply (show denseDrawBits R P d e h ≤ denseRandomBitBudget d b h from ?_).trans
    (denseRandomBitBudget_polynomial d b h)
  unfold denseDrawBits denseTrialBits denseRandomBitBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hoff _)

end

end ContingencyTables.GridBoundary

end OAI
