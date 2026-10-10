import OAI.NumberTheory.Ostmann.Characters.QuartetOrientations
import OAI.NumberTheory.Ostmann.Characters.QuartetFourier

namespace OAI

/-!
# The friendly quartet estimate

The exact held-parameter average is bounded by the uniform Mellin estimate
on one side and total Fourier energy on the other side.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance friendlyQuartetFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem left_friendly_fourier_sum_le {p : ℕ} [Fact p.Prime]
    (P Q : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (δ S : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ (η : MulChar (ZMod p) ℂ) (a : ZMod p),
      (∑ χ : MulChar (ZMod p) ℂ,
        ‖additiveFourier (fun x => P χ x * χ x * η x) a‖ ^ 2) ≤ δ)
    (hQ : (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (Q ψ) a‖ ^ 2) ≤ S)
    (right : Bool) (ν : MulChar (ZMod p) ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (fun x => P χ x * quartetLeftTwist true right ν χ ψ x) a‖ ^ 2 *
      ‖additiveFourier (fun x => Q ψ x * quartetRightTwist true right ν χ ψ x) (-a)‖ ^ 2) ≤
        δ * S := by
  let η : MulChar (ZMod p) ℂ → MulChar (ZMod p) ℂ :=
    fun ψ => ν * (if right then 1 else ψ⁻¹)
  let Q' : MulChar (ZMod p) ℂ → ZMod p → ℂ :=
    fun ψ x => Q ψ x * (ν⁻¹ * (if right then ψ else 1)) x
  have hQ' : (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (Q' ψ) a‖ ^ 2) ≤ S := by
    apply le_trans _ hQ
    exact Finset.sum_le_sum fun ψ _ =>
      additiveFourier_character_energy_le (Q ψ) (ν⁻¹ * (if right then ψ else 1))
  have hleft (χ ψ : MulChar (ZMod p) ℂ) :
      (fun x => P χ x * quartetLeftTwist true right ν χ ψ x) =
        (fun x => P χ x * χ x * η ψ x) := by
    funext x
    simp only [quartetLeftTwist, ite_true, η, MulChar.coeToFun_mul, Pi.mul_apply]
    ring
  have hright (χ ψ : MulChar (ZMod p) ℂ) :
      (fun x => Q ψ x * quartetRightTwist true right ν χ ψ x) = Q' ψ := by
    simp only [quartetRightTwist, ite_true, mul_one, Q']
  simp_rw [hleft, hright]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (MulChar (ZMod p) ℂ)))
    (t := (Finset.univ : Finset (ZMod p)))]
  exact friendly_fourier_sum_le P Q' δ S hδ hP hQ' η

/-- A left-friendly source quartet has the quantitative `src42` bound. -/
theorem quartetParameterValue_left_friendly_bound {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hmixed : MixedFourierBound g ε) (S : ℝ)
    (hS : (∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (pairAutocorrelation h ψ) a‖ ^ 2) ≤ S)
    (right : Bool) (ν : MulChar (ZMod p) ℂ) :
    (p : ℝ)⁻¹ * (∑ y : ZMod p,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ z : (ZMod p)ˣ,
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ t : (ZMod p)ˣ, ‖quartetParameterValue g h true right ν y z t‖ ^ 2)) ≤
      (((p : ℝ) / ((p : ℝ) - 1)) * (ε ^ 4 + Real.sqrt (3 / (p : ℝ)))) * S := by
  rw [quartetParameterValue_parseval]
  apply left_friendly_fourier_sum_le _ _ _ _ _ _ hS right ν
  · have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    positivity
  · intro η a
    exact uniform_mellin_bound_of_fourier_bound g hg henergy ε hmixed η a

end Ostmann

end OAI
