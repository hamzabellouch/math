import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteTypeTorsionLinearGroups
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteCoefficientField

namespace OAI

/-! # Schur's finiteness theorem for characteristic-zero linear groups

A finitely generated torsion group with a faithful finite-dimensional
characteristic-zero matrix representation is finite. The coefficient field,
the uniform eigenvalue-degree bound, and the common exponent are constructed.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

theorem finite_of_faithful_fg_torsion
    {K G : Type} [Field K] [CharZero K] [Group G] [Group.FG G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Function.Injective ι)
    (hpow : ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) : Finite G := by
  obtain ⟨L, hL, hentries⟩ := exists_finite_coefficient_field ι
  let : Algebra.EssFiniteType ℚ L := IntermediateField.essFiniteType_iff.mpr hL
  exact finite_of_faithful_essFiniteType_torsion (restrictCoefficientField ι L hentries)
    (restrictCoefficientField_injective ι L hentries hι) hpow

theorem infinite_fg_linear_group_has_infinite_order
    {K G : Type} [Field K] [CharZero K] [Group G] [Group.FG G] [Infinite G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Function.Injective ι) :
    ∃ g : G, ∀ m : ℕ, 0 < m → g ^ m ≠ 1 := by
  by_contra! h
  have := finite_of_faithful_fg_torsion ι hι h
  exact not_finite G

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
