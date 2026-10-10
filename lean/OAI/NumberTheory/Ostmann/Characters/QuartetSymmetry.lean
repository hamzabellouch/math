import OAI.NumberTheory.Ostmann.Tree.FriendlyQuartet

namespace OAI

/-!
# Interchanging the two bottom pairs

Swapping the pairs inverts the quotient character and negates additive
frequency. This supplies the right-friendly estimate from the left one.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetSymmetryFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def quartetFourierEnergy {p : ℕ} [Fact p.Prime]
    (P Q : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (left right : Bool) (ν : MulChar (ZMod p) ℂ) : ℝ :=
  ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
    ‖additiveFourier (fun x => P χ x * quartetLeftTwist left right ν χ ψ x) a‖ ^ 2 *
    ‖additiveFourier (fun x => Q ψ x * quartetRightTwist left right ν χ ψ x) (-a)‖ ^ 2

theorem quartetFourierEnergy_swap {p : ℕ} [Fact p.Prime]
    (P Q : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (left right : Bool) (ν : MulChar (ZMod p) ℂ) :
    quartetFourierEnergy P Q left right ν = quartetFourierEnergy Q P right left ν⁻¹ := by
  have hL (χ ψ : MulChar (ZMod p) ℂ) :
      quartetLeftTwist left right ν χ ψ = quartetRightTwist right left ν⁻¹ ψ χ := by
    cases left <;> cases right <;>
      simp [quartetLeftTwist, quartetRightTwist, mul_comm, mul_left_comm, mul_assoc]
  have hR (χ ψ : MulChar (ZMod p) ℂ) :
      quartetRightTwist left right ν χ ψ = quartetLeftTwist right left ν⁻¹ ψ χ := by
    cases left <;> cases right <;>
      simp [quartetLeftTwist, quartetRightTwist, mul_comm, mul_assoc]
  unfold quartetFourierEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ψ _
  apply Finset.sum_congr rfl
  intro χ _
  simp_rw [hL, hR]
  calc
    _ = ∑ a : ZMod p,
        ‖additiveFourier (fun x => Q ψ x * quartetLeftTwist right left ν⁻¹ ψ χ x) (-a)‖ ^ 2 *
        ‖additiveFourier (fun x => P χ x * quartetRightTwist right left ν⁻¹ ψ χ x) a‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _
    _ = _ := by
      simpa only [Equiv.neg_apply, neg_neg] using
        (Equiv.neg (ZMod p)).bijective.sum_comp (fun a =>
          ‖additiveFourier (fun x => Q ψ x * quartetLeftTwist right left ν⁻¹ ψ χ x) a‖ ^ 2 *
          ‖additiveFourier (fun x => P χ x * quartetRightTwist right left ν⁻¹ ψ χ x) (-a)‖ ^ 2)

theorem right_friendly_fourier_sum_le {p : ℕ} [Fact p.Prime]
    (P Q : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (δ S : ℝ) (hδ : 0 ≤ δ)
    (hQ : ∀ (η : MulChar (ZMod p) ℂ) (a : ZMod p),
      (∑ ψ : MulChar (ZMod p) ℂ,
        ‖additiveFourier (fun x => Q ψ x * ψ x * η x) a‖ ^ 2) ≤ δ)
    (hP : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (P χ) a‖ ^ 2) ≤ S)
    (left : Bool) (ν : MulChar (ZMod p) ℂ) :
    quartetFourierEnergy P Q left true ν ≤ δ * S := by
  rw [quartetFourierEnergy_swap]
  exact left_friendly_fourier_sum_le Q P δ S hδ hQ hP left ν⁻¹

/-- The symmetric source estimate when the right pair is friendly. -/
theorem quartetParameterValue_right_friendly_bound {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hh : h 0 = 0)
    (henergy : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hmixed : MixedFourierBound h ε) (S : ℝ)
    (hS : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (pairAutocorrelation g χ) a‖ ^ 2) ≤ S)
    (left : Bool) (ν : MulChar (ZMod p) ℂ) :
    (p : ℝ)⁻¹ * (∑ y : ZMod p,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ z : (ZMod p)ˣ,
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ t : (ZMod p)ˣ, ‖quartetParameterValue g h left true ν y z t‖ ^ 2)) ≤
      (((p : ℝ) / ((p : ℝ) - 1)) * (ε ^ 4 + Real.sqrt (3 / (p : ℝ)))) * S := by
  rw [quartetParameterValue_parseval]
  apply right_friendly_fourier_sum_le _ _ _ _ _ _ hS left ν
  · have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    positivity
  · intro η a
    exact uniform_mellin_bound_of_fourier_bound h hh henergy ε hmixed η a

end Ostmann

end OAI
