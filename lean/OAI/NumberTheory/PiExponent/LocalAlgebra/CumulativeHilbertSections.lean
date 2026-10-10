import Mathlib.Algebra.BigOperators.Fin
import OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open MvPolynomial DirectSum
open PiExponentJets.W24 PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem restrictTotalDegree_eq_iSup_homogeneous (n : ℕ) :
    restrictTotalDegree σ k n =
      ⨆ j : Fin (n + 1), homogeneousSubmodule σ k j.val := by
  classical
  apply le_antisymm
  · intro p hp
    have hpdegree : p.totalDegree ≤ n := (mem_restrictTotalDegree σ _ _).mp hp
    have hsum : (∑ j ∈ Finset.range (p.totalDegree + 1), homogeneousComponent j p) ∈
        ⨆ j : Fin (n + 1), homogeneousSubmodule σ k j.val := by
      apply Submodule.sum_mem
      intro j hj
      have hjdegree : j ≤ n :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hpdegree
      exact (le_iSup (fun a : Fin (n + 1) => homogeneousSubmodule σ k a.val)
        ⟨j, Nat.lt_succ_of_le hjdegree⟩) (homogeneousComponent_mem j p)
    simpa only [sum_homogeneousComponent] using hsum
  · apply iSup_le
    intro j p hp
    apply (mem_restrictTotalDegree σ _ _).mpr
    exact (show p.IsHomogeneous j.val from hp).totalDegree_le.trans
      (Nat.le_of_lt_succ j.isLt)

theorem quotientDegreeFiltration_eq_iSup_sections
    (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    quotientDegreeFiltration I n =
      ⨆ j : Fin (n + 1), quotientSection I j.val := by
  unfold quotientDegreeFiltration quotientSection
  rw [restrictTotalDegree_eq_iSup_homogeneous, Submodule.map_iSup]

theorem cumulativeSectionMap_injective (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Function.Injective
      (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val)) :=
  ((quotientSection_iSupIndep I hI).comp Fin.val_injective).dfinsupp_lsum_injective

theorem cumulativeSectionMap_range (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    LinearMap.range
        (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val)) =
      quotientDegreeFiltration I n := by
  rw [DirectSum.range_coeLinearMap, quotientDegreeFiltration_eq_iSup_sections]

def cumulativeHomogeneousQuotientEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    (⨁ j : Fin (n + 1), quotientSection I j.val) ≃ₗ[k]
      quotientDegreeFiltration I n :=
  (LinearEquiv.ofInjective
    (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val))
    (cumulativeSectionMap_injective I hI n)).trans
      (LinearEquiv.ofEq _ _ (cumulativeSectionMap_range I n))

@[simp] theorem cumulativeHomogeneousQuotientEquiv_apply
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ)
    (x : ⨁ j : Fin (n + 1), quotientSection I j.val) :
    (cumulativeHomogeneousQuotientEquiv I hI n x : MvPolynomial σ k ⧸ I) =
      DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val) x := rfl

variable [Finite σ]

theorem quotientDegreeFiltration_finrank_eq_sum_fin
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Module.finrank k (quotientDegreeFiltration I n) =
      ∑ j : Fin (n + 1), Module.finrank k (quotientSection I j.val) := by
  rw [← (cumulativeHomogeneousQuotientEquiv I hI n).finrank_eq,
    Module.finrank_directSum]

theorem quotientDegreeFiltration_finrank_eq_sum
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Module.finrank k (quotientDegreeFiltration I n) =
      ∑ j ∈ Finset.range (n + 1), Module.finrank k (quotientSection I j) := by
  rw [quotientDegreeFiltration_finrank_eq_sum_fin I hI n]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => Module.finrank k (quotientSection I j)) (n + 1)

end PiExponentJets.W25

end

end OAI
