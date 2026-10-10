import OAI.AlgebraicGeometry.StableCoordinate.DeterminantNonzero
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantDomain
import OAI.AlgebraicGeometry.StableCoordinate.LeadingLocallyNilpotent
import OAI.AlgebraicGeometry.StableCoordinate.FactorialClosure

namespace OAI

/-!
# Leading locally nilpotent reduction on the actual determinant ring

This is the auxiliary-grading step in the source's rigidity argument.  The
input is a nonzero locally nilpotent derivation on the concrete determinant
quotient preserving fiber weights and killing the exact obstruction `v`.
The output is a nonzero locally nilpotent derivation with the same fiber
weight property fixing `a`, `d`, and `u`.  All finite generation, grading,
domain, characteristic, and nonvanishing premises are discharged for this
quotient; none is added to the conclusion as an unproved interface.
-/

noncomputable section

namespace StableCoordinate.Obstruction

variable (k : Type*) [Field k] [CharZero k]

/-- The actual leading-component reduction in the determinant quotient.

Auxiliary degrees `-1` and `2` of the two parts of `v` are kept separate,
and compatibility with the second grading retains the fiber weights.
Factorial closure then splits the nonzero difference-of-squares factors.
-/
theorem exists_nonzero_lnd_fixing_a_d_u
    (D : Derivation k (C k) (C k))
    (hD : D ≠ 0) (hln : IsLocallyNilpotent D)
    (hpres : ∀ (n : ℤ) (x : C k), x ∈ fiberPiece k n → D x ∈ fiberPiece k n)
    (hv : D (v k) = 0) :
    ∃ E : Derivation k (C k) (C k), E ≠ 0 ∧ IsLocallyNilpotent E ∧
      (∀ (n : ℤ) (x : C k), x ∈ fiberPiece k n → E x ∈ fiberPiece k n) ∧
      E (cX k 0) = 0 ∧ E (cX k 1) = 0 ∧ E (cX k 4) = 0 := by
  let : IsDomain (C k) := by
    change IsDomain (DeterminantDomain.DeterminantRing k)
    infer_instance
  let : CharZero (C k) := Algebra.charZero_of_charZero k (C k)
  have hv' : D (vLow k + vHigh k) = 0 := by
    rw [← v_eq_low_add_high]
    exact hv
  obtain ⟨m, hm, hnil, hcompatible, htop⟩ :=
    LeadingComponent.exists_nonzero_locallyNilpotent_component_compatible
      (auxiliaryPiece k) (fiberPiece k) (auxiliary_fiber_proj_commute k)
      (cX k) auxiliaryWeight (adjoin_range_cX k) (cX_mem_auxiliaryPiece k)
      D hD hln hpres (vLow_mem_auxiliaryPiece k) (vHigh_mem_auxiliaryPiece k)
      (by decide : (-1 : ℤ) < 2) hv'
  let E := LeadingComponent.component (auxiliaryPiece k) D m
  have hfixed : E (cX k 0) = 0 ∧ E (cX k 1) = 0 ∧ E (cX k 4) = 0 :=
    lnd_fixed_of_difference_of_squares E hnil
      (cX_a_ne_zero k) (cX_u_ne_zero k)
      (au_sub_d_ne_zero k) (au_add_d_ne_zero k) htop
  exact ⟨E, hm, hnil, hcompatible, hfixed⟩

end StableCoordinate.Obstruction

end

end OAI
