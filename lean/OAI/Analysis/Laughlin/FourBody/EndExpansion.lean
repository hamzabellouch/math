import OAI.Analysis.Laughlin.FourBody.ColumnExpansion

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem occupationInner_left_ext (Q : ℕ) (x y : Space Q)
    (h : ∀ z, occupationInner Q x z = occupationInner Q y z) : x=y := by
  apply (occupationBasis Q).repr.injective
  ext A
  have hA := h (occupationBasis Q A)
  rw [occupationInner_basis_right,occupationInner_basis_right] at hA
  exact star_injective hA

theorem limitFourCopyEnd_expansion (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
    limitFourCopyEnd Q r D x = ∑ A : FourOccupation Q D,
      (fourOccupationCoefficient Q r D A.val : ℂ) • fourOccupationEnd Q D A x := by
  apply occupationInner_left_ext
  intro y
  rw [← limitFourColumn_mul_adjoint,limitFourColumn_expansion Q r D hr hor]
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_right,occupationInner_sum_left,
    occupationInner_smul_right,occupationInner_smul_left,Complex.star_def,Complex.conj_ofReal,
    ← fourOccupationCreate_mul,fourOccupation_adjoint]

end Laughlin.Fock

end OAI
