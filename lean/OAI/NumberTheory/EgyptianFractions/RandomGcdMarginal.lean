import OAI.NumberTheory.EgyptianFractions.RandomGcdBound
import OAI.NumberTheory.EgyptianFractions.SampleWordTransfer

namespace OAI
open scoped BigOperators

namespace Problem337.RandomProducts

/-- Typed-sample form of the concrete reduced-modulus exceptional-event bound. -/
theorem random_gcd_typed_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 2 ≤ S) (hV : 0 ≤ V) (hVS : V ≤ S)
    (huexp : (u : ℝ) = Real.exp V) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (ht : (Fintype.card ι : ℝ) ≤ S) (hsize : S ^ 99 ≤ (P.card : ℝ))
    (hl : 0 < l) (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (Fintype.card {f : ι → P //
      ((u / Nat.gcd (l * ∏ i, (f i : ℕ)) u : ℕ) : ℝ) < Real.exp (9 * V / 10)} : ℝ) /
        (Fintype.card (ι → P) : ℝ) ≤ Real.exp (-V / 20) := by
  rw [typed_product_event_probability P
    (fun n => ((u / Nat.gcd (l * n) u : ℕ) : ℝ) < Real.exp (9 * V / 10))]
  exact random_gcd_exception_bound_wide P (Fintype.card ι) u l S V
    hP hS hV hVS huexp hprime hinterval ht hsize hl hlbound

/-- An exposed product may use only some of the exposed coordinates. Other exposed
samples do not change its exceptional-event probability: the exact uniform marginal
identity reduces it to the independently sampled product bound. -/
theorem random_gcd_marginal_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (A : Finset ι) (u l : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 2 ≤ S) (hV : 0 ≤ V) (hVS : V ≤ S)
    (huexp : (u : ℝ) = Real.exp V) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (ht : (A.card : ℝ) ≤ S) (hsize : S ^ 99 ≤ (P.card : ℝ))
    (hl : 0 < l) (hlbound : (l : ℝ) ≤ Real.exp (V / 200)) :
    (Fintype.card {f : ι → P //
      ((u / Nat.gcd (l * ∏ i : A, (f i : ℕ)) u : ℕ) : ℝ) < Real.exp (9 * V / 10)} : ℝ) /
        (Fintype.card (ι → P) : ℝ) ≤ Real.exp (-V / 20) := by
  classical
  let : Nonempty P := by obtain ⟨p, hp⟩ := hP; exact ⟨⟨p, hp⟩⟩
  rw [restricted_product_event_probability P A
    (fun n => ((u / Nat.gcd (l * n) u : ℕ) : ℝ) < Real.exp (9 * V / 10))]
  exact random_gcd_exception_bound_wide P (Fintype.card A) u l S V
    hP hS hV hVS huexp hprime hinterval (by simpa only [Fintype.card_coe] using ht)
    hsize hl hlbound

end Problem337.RandomProducts

end OAI
