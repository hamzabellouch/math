import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Foundations.Conditioning

namespace OAI

section

/-! A finite experiment whose sample weights are constant on the selected
event becomes exactly uniform after conditioning on that event. The event is
allowed to have arbitrary positive mass, so this applies after the complete
visible datum and the chosen column constraints have both been fixed. -/

namespace UniqueGamesTheorem.Decoder.UniformConditioning

open Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem sum_over_event (given : Ω → Bool) (f : Ω → ℝ) :
    (∑ x, if given x then f x else 0) = ∑ x : {x : Ω // given x = true}, f x.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun x => by simp) f

theorem probability_as_subtype_sum (μ : FiniteDistribution Ω) (given : Ω → Bool) :
    μ.probability given = ∑ x : {x : Ω // given x = true}, μ.weight x.val :=
  sum_over_event given μ.weight

theorem probability_and_as_subtype_sum (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) :
    μ.probability (fun x => given x && event x) =
      ∑ x : {x : Ω // given x = true}, if event x.val then μ.weight x.val else 0 := by
  calc
    _ = ∑ x, if given x then (if event x then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      change (if given x && event x then μ.weight x else 0) = _
      cases given x <;> cases event x <;> rfl
    _ = _ := sum_over_event given _

theorem probability_of_constant_weight (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (c : ℝ) (hconstant : ∀ x, given x = true → μ.weight x = c) :
    μ.probability given = (Fintype.card {x : Ω // given x = true} : ℝ) * c := by
  rw [probability_as_subtype_sum]
  calc
    _ = ∑ _x : {x : Ω // given x = true}, c := by
      apply Finset.sum_congr rfl
      intro x _
      exact hconstant x.val x.property
    _ = _ := by simp [nsmul_eq_mul]

/-- Every remaining point receives equal conditional weight. Positivity of
the conditioning event justifies cancellation; no unconditional uniform law
on the original ambient experiment is required. -/
theorem condition_probability_uniform (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given)
    (c : ℝ) (hconstant : ∀ x, given x = true → μ.weight x = c) :
    (μ.condition given positive).probability event =
      𝔼 x : {x : Ω // given x = true}, if event x.val then (1 : ℝ) else 0 := by
  have hp := probability_of_constant_weight μ given c hconstant
  have hc : c ≠ 0 := by
    intro hz
    rw [hp, hz, mul_zero] at positive
    exact (lt_irrefl 0) positive
  have hn : (Fintype.card {x : Ω // given x = true} : ℝ) ≠ 0 := by
    intro hz
    rw [hp, hz, zero_mul] at positive
    exact (lt_irrefl 0) positive
  rw [FiniteDistribution.probability_condition, probability_and_as_subtype_sum, hp,
    Fintype.expect_eq_sum_div_card]
  have hnum : (∑ x : {x : Ω // given x = true}, if event x.val then μ.weight x.val else 0) =
      c * ∑ x : {x : Ω // given x = true}, if event x.val then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [hconstant x.val x.property]
    cases event x.val <;> simp
  rw [hnum]
  field_simp [hc, hn]

/-- A proved bijection with the actual affine matrix slice identifies the
conditional target probability with that slice's complete uniform average. -/
theorem condition_probability_equiv {Y : Type*} [Fintype Y]
    (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) (c : ℝ)
    (hconstant : ∀ x, given x = true → μ.weight x = c)
    (e : {x : Ω // given x = true} ≃ Y) (target : Y → Bool)
    (hevent : ∀ x, event x.val = target (e x)) :
    (μ.condition given positive).probability event =
      𝔼 y : Y, if target y then (1 : ℝ) else 0 := by
  rw [condition_probability_uniform μ given event positive c hconstant]
  apply Fintype.expect_equiv e
  intro x
  rw [hevent x]

end
end UniqueGamesTheorem.Decoder.UniformConditioning

end

end OAI
