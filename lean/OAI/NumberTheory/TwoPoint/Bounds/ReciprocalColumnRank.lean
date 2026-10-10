import OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
import OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalLaw

namespace OAI

/-! The finite positive reciprocal majorant for one high-rank column. -/

namespace TwoPointCorrelations.ColumnWordPattern

open Finset
open scoped Classical

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- A single reciprocal factor is retained for each abstract label. The
sum permits numerical collisions and is uniform in all fixed other-column
data and the starting point of the word. -/
theorem reciprocal_high_rank_bound
    (w : ColumnWordPattern α) (h Q D B H : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hV : 0 < primeHarmonicMass P) (hH : 0 < H)
    (hlo : ∀ p ∈ P, H ≤ p) (hbound : ∀ p ∈ P, p ≤ B)
    (hq : ∀ j < w.length, w.padding j ≤ Q)
    (hd : ∀ j < w.length, w.otherColumns j ≤ D)
    (left right : ρ → ℕ) (control : ρ → α)
    (hl : ∀ i, left i ≤ w.length) (hr : ∀ i, right i ≤ w.length)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture w.label (fun j => (w.coefficient h j : ℝ)) (left i) -
        formalDeparture w.label (fun j => (w.coefficient h j : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ α (control i))))
    (base : (α → P) → ℤ) (E : (α → P) → Prop)
    (hlit : ∀ x, E x → ∀ i, ((x (control i)).val : ℤ) ∣ base x +
      wordDisplacement h ((w.word (fun z => (x z).val)).take (left i)))
    (hrit : ∀ x, E x → ∀ i, ((x (control i)).val : ℤ) ∣ base x +
      wordDisplacement h ((w.word (fun z => (x z).val)).take (right i))) :
    (∑ x : α → P, if E x then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      primeHarmonicMass P ^ Fintype.card α *
        Real.sqrt (((primeHarmonicMass P * H)⁻¹ *
          (1 + (Nat.log 2 (2 * w.length * (h * Q * D) * B) : ℝ))) ^ Fintype.card ρ) := by
  apply primeReciprocalLaw_restore_bound P hV E
  exact w.high_rank_event_bound h Q D B P hP (primeReciprocalLaw P hV)
    hbound hq hd left right control hl hr hind (primeHarmonicMass P * H)⁻¹
    (by positivity) (primeReciprocalLaw_atom_le P hV H hH hlo) base E hlit hrit

end TwoPointCorrelations.ColumnWordPattern

end OAI
