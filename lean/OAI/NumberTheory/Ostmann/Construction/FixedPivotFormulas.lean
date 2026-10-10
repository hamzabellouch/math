import OAI.NumberTheory.Ostmann.Construction.ExpandedHistoryFormula

namespace OAI

/-! # Removing the fixed pivot from the independent polynomial variables -/

namespace Ostmann.HistoryFormula

open scoped Classical

def fixNone {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) : HistoryFormula V :=
  F.bind (fun i => match i with | none => .external M | some v => .prime v)

theorem fixNone_value {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) (x : V → ℤ) :
    (F.fixNone M).value (fun i => (x i : ℚ)) =
      F.value (fun i => match i with | none => (M : ℚ) | some v => (x v : ℚ)) := by
  rw [fixNone, value_bind]
  congr 1
  funext i
  cases i <;> simp only [value_external, value_prime]

theorem fixNone_cost {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) :
    (F.fixNone M).cost = F.cost := by
  induction F with
  | prime i => cases i <;> rfl
  | external z => rfl
  | product f g ihf ihg => exact congrArg₂ (· + ·) ihf ihg
  | solve f g v w s hs ihf ihg =>
    change (f.fixNone M).cost + (g.fixNone M).cost + 2 = f.cost + g.cost + 2
    rw [ihf, ihg]

theorem fixNone_frequencies {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) :
    (F.fixNone M).frequencies = F.frequencies := by
  induction F with
  | prime i => cases i <;> rfl
  | external z => rfl
  | product f g ihf ihg => exact congrArg₂ List.append ihf ihg
  | solve f g v w s hs ihf ihg => exact congrArg (s :: ·) (congrArg₂ List.append ihf ihg)

theorem fixNone_denominator {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) :
    (F.fixNone M).cleared.denominator = F.cleared.denominator := by
  rw [denominator_eq_frequency_product, fixNone_frequencies, denominator_eq_frequency_product]

theorem fixNone_inputs {V : Type*} (M : ℤ) (F : HistoryFormula (Option V))
    (R : ℝ) (hM : |(M : ℝ)| ≤ R) (hF : F.InputsBounded R) :
    (F.fixNone M).InputsBounded R := by
  apply inputsBounded_bind F _ R hF
  intro i
  cases i
  · exact hM
  · trivial

def fixedOriginalPrimes {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n)) : HistoryFormula V :=
  F.originalPrimes.fixNone M

theorem fixedOriginalPrimes_value {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n)) (x : V → ℤ) :
    (F.fixedOriginalPrimes M).value (fun i => (x i : ℚ)) =
      F.value (fun i => (expandedPrimeValues n (fun i => match i with
        | none => M | some v => x v) i : ℚ)) := by
  rw [fixedOriginalPrimes, fixNone_value]
  have he : (fun i : Option V => match i with | none => (M : ℚ) | some v => (x v : ℚ)) =
      (fun i : Option V => (((match i with | none => M | some v => x v) : ℤ) : ℚ)) := by
    funext i
    cases i <;> rfl
  rw [he]
  exact F.originalPrimes_value (fun i => match i with | none => M | some v => x v)

theorem fixedOriginalPrimes_cost {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n)) :
    (F.fixedOriginalPrimes M).cost = F.cost := by
  rw [fixedOriginalPrimes, fixNone_cost, originalPrimes_cost]

theorem fixedOriginalPrimes_denominator {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n)) :
    (F.fixedOriginalPrimes M).cleared.denominator = F.cleared.denominator := by
  rw [fixedOriginalPrimes, fixNone_denominator, originalPrimes_denominator]

theorem fixedOriginalPrimes_inputs {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n))
    (R : ℝ) (hR : 1 ≤ R) (hM : |(M : ℝ)| ≤ R) (hF : F.InputsBounded R) :
    (F.fixedOriginalPrimes M).InputsBounded R :=
  F.originalPrimes.fixNone_inputs M R hM (F.originalPrimes_inputs R hR hF)

theorem fixedOriginalPrimes_integer_value {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n)) (x : V → ℤ) (y : ℤ)
    (hy : F.value (fun i => (expandedPrimeValues n (fun i => match i with
      | none => M | some v => x v) i : ℚ)) = y) :
    MvPolynomial.eval₂Hom (RingHom.id ℤ) x (F.fixedOriginalPrimes M).cleared.numerator =
      F.cleared.denominator * y := by
  rw [← fixedOriginalPrimes_denominator M F]
  apply ClearedHistoryValue.integer_value_cleared
  exact (F.fixedOriginalPrimes_value M x).trans hy

end Ostmann.HistoryFormula

end OAI
