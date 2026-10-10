import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthNilpotentCentralLayers
import OAI.GroupTheory.PolycyclicRecognition.Lattices.PolycyclicLatticeRealization
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthSubgroups
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvablePolynomialGrowthPolycyclic
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteKernelAscendingBase

namespace OAI

/-! # Polynomial growth of virtually polycyclic groups

Polynomial growth forces virtual nilpotence. The finite-index passage to
finite integral dimension and the central-layer argument are both proved;
no Milnor--Wolf conclusion is assumed here.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] [DecidableEq G]

theorem polycyclic_polynomial_growth_virtually_nilpotent
    (hpoly : IsPolycyclic G)
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) :
    Group.IsVirtuallyNilpotent G := by
  classical
  let : Group.FG G := hpoly.finitelyGenerated
  obtain ⟨H, hHi, hHs, hHcd⟩ := hpoly.exists_solvable_finiteDimension
  let := hHi
  let := hHs
  obtain ⟨C, d, hvol⟩ := hvol
  obtain ⟨T, hT, hTgen, M, hM⟩ := polynomial_growth_fg_subgroup S hS hgen C d hvol H
  apply virtuallyNilpotent_of_finiteIndex H
  exact polynomial_growth_nilpotent_finiteIndex_of_finiteDimension
    (hpoly.of_injective H.subtype Subtype.val_injective) hHcd T hT hTgen ⟨M, d, hM⟩

theorem virtually_polycyclic_polynomial_growth_virtually_nilpotent
    (hpoly : IsVirtuallyPolycyclic G)
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) :
    Group.IsVirtuallyNilpotent G := by
  classical
  obtain ⟨H, hHi, hHpoly⟩ := hpoly
  let := hHi
  let : Group.FG H := hHpoly.finitelyGenerated
  obtain ⟨C, d, hvol⟩ := hvol
  obtain ⟨T, hT, hTgen, M, hM⟩ := polynomial_growth_fg_subgroup S hS hgen C d hvol H
  exact virtuallyNilpotent_of_finiteIndex H
    (polycyclic_polynomial_growth_virtually_nilpotent hHpoly T hT hTgen ⟨M, d, hM⟩)

theorem virtually_solvable_polynomial_growth_virtually_nilpotent
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (H : Subgroup G) [H.FiniteIndex] [Group.IsSolvable H] :
    Group.IsVirtuallyNilpotent G := by
  let : Group.FG G := Group.fg_def.mpr ⟨S, hgen⟩
  exact virtually_polycyclic_polynomial_growth_virtually_nilpotent
    (virtually_solvable_polynomial_growth_virtually_polycyclic S hS hgen hvol H)
    S hS hgen hvol

end PolycyclicRecognition

end

end OAI
