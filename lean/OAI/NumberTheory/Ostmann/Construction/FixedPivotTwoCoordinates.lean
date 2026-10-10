import OAI.NumberTheory.Ostmann.Construction.FixedPivotPrimeChecks
import OAI.NumberTheory.Ostmann.Construction.OriginalHarmonicPair

namespace OAI

/-! # A fixed integer outside the two selected original prime coordinates -/

namespace Ostmann

open scoped BigOperators Classical

def fixedPivotOutside {V : Type*} (a b : V) (M : ℕ)
    (outside : OtherVertices a b → ℕ) : OtherVertices (some a) (some b) → ℕ :=
  fun i => match h : i.val with
  | none => M
  | some v => outside ⟨v, fun hv => i.property.1 (h.trans (congrArg some hv)),
      fun hv => i.property.2 (h.trans (congrArg some hv))⟩

theorem fixedPivotPrimeValues_twoCoordinates {V : Type*} (a b : V) (hab : a ≠ b)
    (M : ℕ) (outside : OtherVertices a b → ℕ) (q p : ℕ) :
    fixedPivotPrimeValues M (twoCoordinateAssignment a b hab outside q p) =
      twoCoordinateAssignment (some a) (some b) (fun h => hab (Option.some.inj h))
        (fixedPivotOutside a b M outside) q p := by
  funext i
  cases i with
  | none =>
    have hn : (none : Option V) ≠ some a ∧ (none : Option V) ≠ some b := by simp
    simpa only [fixedPivotPrimeValues, fixedPivotOutside] using
      (twoCoordinateAssignment_other (some a) (some b) _
        (fixedPivotOutside a b M outside) q p ⟨none, hn⟩).symm
  | some v =>
    by_cases ha : v = a
    · subst v
      simp only [fixedPivotPrimeValues, twoCoordinateAssignment_short]
    by_cases hb : v = b
    · subst v
      simp only [fixedPivotPrimeValues, twoCoordinateAssignment_long]
    have hs : some v ≠ some a ∧ some v ≠ some b :=
      ⟨fun h => ha (Option.some.inj h), fun h => hb (Option.some.inj h)⟩
    have h1 := twoCoordinateAssignment_other a b hab outside q p ⟨v, ha, hb⟩
    have h2 := twoCoordinateAssignment_other (some a) (some b) (fun h => hab (Option.some.inj h))
      (fixedPivotOutside a b M outside) q p ⟨some v, hs⟩
    simpa only [fixedPivotPrimeValues, fixedPivotOutside] using h1.trans h2.symm

theorem fixed_pivot_original_harmonic_pair_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) (M : ℕ) (P : Finset ℕ) (Q : V → Finset ℕ)
    (hQP : ∀ v, Q v ⊆ P) (hQmass : ∀ v, (∑ q ∈ Q v, (q : ℝ)⁻¹) ≠ 0)
    (F : (Option V → ℕ) → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsection : ∀ outside : OtherVertices (some a) (some b) → ℕ,
      ‖∑ p : Q b, (primeSubsetPrior (Q b) (Q b) p : ℂ) *
        ∑ q : Q a, (primeSubsetPrior (Q a) (Q a) q : ℂ) *
          F (twoCoordinateAssignment (some a) (some b)
            (fun h => hab (Option.some.inj h)) outside (q : ℕ) (p : ℕ))‖ ≤ δ) :
    ‖∑ x : V → P, ((∏ v, primeSubsetPrior P (Q v) (x v) : ℝ) : ℂ) *
      F (fixedPivotPrimeValues M (fun v => (x v : ℕ)))‖ ≤ δ := by
  apply original_harmonic_pair_bound a b hab P Q hQP hQmass
    (fun x => F (fixedPivotPrimeValues M x)) δ hδ
  intro outside
  simp_rw [fixedPivotPrimeValues_twoCoordinates]
  exact hsection (fixedPivotOutside a b M (fun i => (outside i : ℕ)))

end Ostmann

end OAI
