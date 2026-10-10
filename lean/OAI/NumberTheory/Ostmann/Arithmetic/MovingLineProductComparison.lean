import OAI.NumberTheory.Ostmann.Arithmetic.MovingLineIntegration

namespace OAI

/-! # Signed joint arithmetic comparison with the actual line integrals -/

namespace Ostmann
open scoped BigOperators Classical

/-- This replaces the actual simultaneous line probabilities, under the
original product law, by their symbolic rank and feasibility flags. The
support may contain any further arithmetic and smooth restrictions. -/
theorem moving_slot_line_product_comparison {A J O : Type*}
    [Fintype A] [Nonempty A] [Fintype J] [Fintype O] {n : ℕ}
    (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (path : J → O → List (MovingSlotReversal (Fin (n + 1))))
    (current : J → O → MovingSlotReversal (Fin (n + 1)))
    (base : J → O) (coordinate : J → Fin (n + 1)) (external : J → Bool)
    (k d : ℕ) (F T : ℝ) (hF : 1 ≤ F) (hT : 1 ≤ T)
    (hlen : ∀ j o, (path j o).length ≤ k)
    (hd : ∀ j o, (∀ s ∈ path j o, s.lengthLE d ∧ s.frequencyLE F) ∧
      (current j o).lengthLE d ∧ (current j o).frequencyLE F)
    (habsent : ∀ j o,
      (∀ s ∈ path j o, coordinate j ∉ s.leftSlots ∧ coordinate j ∉ s.rightSlots ∧
        coordinate j ∉ s.compensationSlots) ∧
      coordinate j ∉ (current j o).leftSlots ∧ coordinate j ∉ (current j o).rightSlots)
    (hvalues : ∀ a, |(value a : ℝ)| ≤ T)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coordinate j) a ≤ β)
    (hsize : ∀ j a, μ (coordinate j) a ≠ 0 → V ≤ Real.log (prime a : ℝ))
    (weight : (Fin (n + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hweight : ∀ x, ‖weight x‖ *
      ∏ j, internalLineScalar (external j) (prime (x (coordinate j))) ≤ B)
    (hpath : ∀ x, weight x ≠ 0 → ∀ j o s, s ∈ path j o →
      let φ := integerLineReduction value x (prime (x (coordinate j)))
      φ s.polynomial.v ≠ 0 ∧ φ s.polynomial.w ≠ 0 ∧ φ s.polynomial.u ≠ 0)
    (hcurrent : ∀ x, weight x ≠ 0 → ∀ j,
      let φ := integerLineReduction value x (prime (x (coordinate j)))
      φ (current j (base j)).polynomial.v ≠ 0 ∧ φ (current j (base j)).polynomial.w ≠ 0) :
    ‖∑ x, (productPrior μ x : ℂ) * weight x *
      ((∏ j, (movingSlotLineProbability value prime hprime (path j) (current j)
          (external j) x (x (coordinate j)) : ℂ)) -
       ∏ j, (internalLineFlagWeight (external j) (prime (x (coordinate j)))
          (fun s => arithmeticTestFlag (lineTestPolynomials
            (fun o => movingSlotLine (path j o) (current j o)) (base j) s = 0)) : ℂ))‖ ≤
      2 * B * (Fintype.card J * (2 + Fintype.card O)) *
        ((2 * ((k + 1) * d) : ℕ) * α +
          (Real.log (2 * ((2 * (F * T ^ d)) ^ (k + 1)) ^ 2) / V) * β) := by
  let Ψ := fun (x : Fin (n + 1) → A) (flags : J × (Bool ⊕ O) → Bool) =>
    weight x * ∏ j, (internalLineFlagWeight (external j) (prime (x (coordinate j)))
      (fun s => flags (j, s)) : ℂ)
  have hΨ (x : Fin (n + 1) → A) (flags : J × (Bool ⊕ O) → Bool) : ‖Ψ x flags‖ ≤ B :=
    line_product_multiplier_bound prime external (fun j => x (coordinate j)) (weight x) B
      (hweight x) flags
  have h := moving_slot_joint_symbolic_comparison value hinj prime hpInj hprime
    path current base coordinate k d F T hF hT hlen hd habsent hvalues μ hμ hmass
    α β V hα hβ hV hmax hpmax hsize Ψ B hB hΨ
  have he (x : Fin (n + 1) → A) := moving_line_product_on_support value prime hprime
    path current base external (fun j => x (coordinate j)) x (weight x) (hpath x) (hcurrent x)
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  dsimp only [Ψ]
  rw [mul_sub, mul_assoc, he, ← mul_sub]
  ring

end Ostmann

end OAI
