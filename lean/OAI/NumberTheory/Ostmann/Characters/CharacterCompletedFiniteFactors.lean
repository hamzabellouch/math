import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterCompletedZeros
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteAnalyticZeroFactors

namespace OAI

/-! # Consequences of a finite nontrivial zero set for the completed function -/

namespace Ostmann

open Set
open scoped Classical

theorem character_completed_finite_factors (χ : PrimitiveComplexCharacter)
    (hfinite : (complexCharacterZeros χ).Finite) :
    ∃ g : ℂ → ℂ, (∀ s, AnalyticAt ℂ g s) ∧ (∀ s, g s ≠ 0) ∧
      ∀ s, χ.completed s = finiteZeroPolynomial χ.completed hfinite.toFinset s * g s := by
  obtain ⟨g, hg, he, hgne⟩ := remove_finite_analytic_zeros χ.completed
    χ.completed_analytic χ.completed_order_ne_top hfinite.toFinset
  refine ⟨g, hg, ?_, he⟩
  intro s
  by_cases hs : s ∈ hfinite.toFinset
  · exact hgne s hs
  · intro hzero
    have hc : χ.completed s = 0 := by rw [he, hzero, mul_zero]
    exact hs (hfinite.mem_toFinset.mpr ((χ.completed_zero_iff s).mp hc))

end Ostmann

end OAI
