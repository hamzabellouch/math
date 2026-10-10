import OAI.AlgebraicGeometry.StableCoordinate.DeterminantLeadingReduction
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantFinalStep
import OAI.AlgebraicGeometry.StableCoordinate.VerticalLND

namespace OAI

/-!
# Rigidity of the weighted determinant hypersurface

This is Proposition `prop:rigidity` of Section 5 of the paper,
on the actual quotient `k[a,d,b,c,u]/(ac-bd-1)`, with the two actual quotient
gradings and the exact element `v = a^3*b + a^2*u^2 - d^2`.

All intermediate existence and regularity claims are proved: the leading
locally nilpotent component, factorial closure, the two localized polynomial
charts, the two-denominator intersection, and the negative-weight obstruction.
There is no domain, chart, polynomiality, or auxiliary-grading hypothesis in
the final statement.
-/

namespace StableCoordinate.Obstruction

variable (k : Type*) [Field k] [CharZero k]

/-- A locally nilpotent derivation preserving the source fiber weights and
annihilating the source element `v` is zero. -/
theorem weight_preserving_lnd_killing_v_eq_zero
    (D : Derivation k (C k) (C k))
    (hln : IsLocallyNilpotent D)
    (hpres : ∀ (n : ℤ) (x : C k), x ∈ fiberPiece k n → D x ∈ fiberPiece k n)
    (hv : D (v k) = 0) : D = 0 := by
  by_contra hD
  obtain ⟨E, hE, hnil, hgraded, ha, hd, hu⟩ :=
    exists_nonzero_lnd_fixing_a_d_u k D hD hln hpres hv
  exact hE (DeterminantRing.derivation_eq_zero_of_fixed_base_and_coefficient_mem k E
    ha hd hu hgraded (VerticalLND.coefficient_mem_baseRange E hnil ha hd hu))

/-- The nonexistence form of `prop:rigidity`, retaining every derivation in
the quantifier rather than restricting to explicitly constructed actions. -/
theorem no_nonzero_lnd_preserving_fiber_weights_killing_v :
    ¬ ∃ D : Derivation k (C k) (C k), D ≠ 0 ∧ IsLocallyNilpotent D ∧
      (∀ (n : ℤ) (x : C k), x ∈ fiberPiece k n → D x ∈ fiberPiece k n) ∧
      D (v k) = 0 := by
  rintro ⟨D, hD, hln, hpres, hv⟩
  exact hD (weight_preserving_lnd_killing_v_eq_zero k D hln hpres hv)

end StableCoordinate.Obstruction

end OAI
