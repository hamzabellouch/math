import OAI.NumberTheory.Ostmann.Characters.CharacterFunctionalEquation

namespace OAI

/-! # Functional-equation symmetry preserves zero multiplicity -/

namespace Ostmann

open Filter Set
open scoped Topology

theorem PrimitiveComplexCharacter.completed_order_reflection (χ : PrimitiveComplexCharacter)
    (s : ℂ) : analyticOrderAt χ.completed (1 - s) =
      analyticOrderAt χ.inverse.completed s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let G : ℂ → ℂ := fun z => (χ.modulus : ℂ) ^ (z - 1 / 2) *
    DirichletCharacter.rootNumber χ.character
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hG : AnalyticAt ℂ G s :=
    (((differentiable_id.sub_const (1 / 2 : ℂ)).const_cpow (.inl hq)).mul_const
      (DirichletCharacter.rootNumber χ.character)).analyticAt s
  have hGne : G s ≠ 0 := mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl hq)) χ.rootNumber_ne_zero
  have he : χ.completed ∘ (fun z => 1 - z) = G * χ.inverse.completed := by
    funext z
    exact χ.primitive.completedLFunction_one_sub z
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := χ.completed) (z₀ := s)
    (show AnalyticAt ℂ (fun z => 1 - z) s from analyticAt_const.sub analyticAt_id)
    (show deriv (fun z : ℂ => 1 - z) s ≠ 0 by
      change deriv (fun z : ℂ => 1 - id z) s ≠ 0
      rw [((hasDerivAt_id s).const_sub (1 : ℂ)).deriv]
      norm_num)
  rw [he, analyticOrderAt_mul hG (χ.inverse.completed_analytic s),
    hG.analyticOrderAt_eq_zero.mpr hGne, zero_add] at hcomp
  exact hcomp.symm

theorem PrimitiveComplexCharacter.L_order_reflection (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    analyticOrderAt χ.L (1 - s) = analyticOrderAt χ.inverse.L s := by
  rw [χ.L_order_eq_completed (1 - s) (by simp; linarith),
    χ.inverse.L_order_eq_completed s hs]
  exact χ.completed_order_reflection s

theorem characterZeroOrder_reflection (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    characterZeroOrder χ (1 - s) = characterZeroOrder χ.inverse s := by
  rw [characterZeroOrder, characterZeroOrder,
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z) (mem_univ _),
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      (show AnalyticOnNhd ℂ χ.inverse.L univ from fun z _ => χ.inverse.L_analytic z) (mem_univ _),
    χ.L_order_reflection s hs hs']

end Ostmann

end OAI
