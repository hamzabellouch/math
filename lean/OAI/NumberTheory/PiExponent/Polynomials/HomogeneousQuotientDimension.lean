import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open MvPolynomial
open PiExponentJets.W64
open DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

def quotientDegreeProjection (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (n : ℕ) :
    (MvPolynomial σ k ⧸ I) →ₗ[k] (MvPolynomial σ k ⧸ I) :=
  (I.restrictScalars k).liftQ
    ((Ideal.Quotient.mkₐ k I).toLinearMap.comp
      (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n)) (by
    intro p hp
    change Ideal.Quotient.mk I
      (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n p) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (Ideal.IsHomogeneous.mem_iff
      (MvPolynomial.homogeneousSubmodule σ k) hI).mp hp n)

@[simp] theorem quotientDegreeProjection_mk (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (n : ℕ)
    (p : MvPolynomial σ k) :
    quotientDegreeProjection I hI n (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk I
        (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n p) := rfl

theorem quotientDegreeProjection_of_mem (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n m : ℕ) (x : MvPolynomial σ k ⧸ I) (hx : x ∈ quotientSection I m) :
    quotientDegreeProjection I hI n x = if n = m then x else 0 := by
  obtain ⟨p, hp, rfl⟩ := hx
  change quotientDegreeProjection I hI n (Ideal.Quotient.mk I p) = _
  rw [quotientDegreeProjection_mk, GradedAlgebra.proj_apply]
  by_cases hnm : n = m
  · subst n
    rw [DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp]
    simp
  · rw [DirectSum.decompose_of_mem_ne (MvPolynomial.homogeneousSubmodule σ k) hp
      (Ne.symm hnm)]
    simp [hnm]

theorem quotientSection_iSupIndep (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    iSupIndep (quotientSection I) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  have hcalc : quotientDegreeProjection I hI i (∑ j ∈ s, v j) = v i := by
    rw [map_sum]
    calc
      ∑ j ∈ s, quotientDegreeProjection I hI i (v j) =
          ∑ j ∈ s, if i = j then v j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact quotientDegreeProjection_of_mem I hI i j (v j) (hv j hj)
      _ = v i := by simp [hi]
  rw [hsum, map_zero] at hcalc
  exact hcalc.symm

theorem quotientSection_iSup_eq_top (I : Ideal (MvPolynomial σ k)) :
    (⨆ n, quotientSection I n) = ⊤ := by
  simp only [quotientSection, ← Submodule.map_iSup]
  rw [(DirectSum.Decomposition.isInternal
    (MvPolynomial.homogeneousSubmodule σ k)).submodule_iSup_eq_top]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective k I)

theorem quotientSection_isInternal (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    DirectSum.IsInternal (quotientSection I) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (quotientSection_iSupIndep I hI) (quotientSection_iSup_eq_top I)

def homogeneousQuotientDirectSumEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (⨁ n : ℕ, quotientSection I n) ≃ₗ[k] (MvPolynomial σ k ⧸ I) :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (quotientSection I))
    (quotientSection_isInternal I hI)

theorem quotientSection_bounded_iSup_eq_top (I : Ideal (MvPolynomial σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    (⨆ n : Fin (B+1), quotientSection I n.val) = ⊤ := by
  rw [← quotientSection_iSup_eq_top I]
  apply le_antisymm
  · exact iSup_le fun n => le_iSup (quotientSection I) n.val
  · apply iSup_le
    intro n
    by_cases hn : n < B+1
    · exact le_iSup (fun j : Fin (B+1) => quotientSection I j.val) ⟨n, hn⟩
    · rw [hzero n (Nat.lt_of_succ_le (Nat.le_of_not_lt hn))]
      exact bot_le

def boundedHomogeneousQuotientEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    (⨁ n : Fin (B+1), quotientSection I n.val) ≃ₗ[k] (MvPolynomial σ k ⧸ I) :=
  LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun n : Fin (B+1) => quotientSection I n.val))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      ((quotientSection_iSupIndep I hI).comp Fin.val_injective)
      (quotientSection_bounded_iSup_eq_top I B hzero))

variable [Finite σ]

theorem homogeneousQuotient_finite (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    Module.Finite k (MvPolynomial σ k ⧸ I) :=
  Module.Finite.equiv (boundedHomogeneousQuotientEquiv I hI B hzero)

theorem homogeneousQuotient_finrank_eq_sum (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    Module.finrank k (MvPolynomial σ k ⧸ I) =
      ∑ n : Fin (B+1), Module.finrank k (quotientSection I n.val) := by
  rw [← (boundedHomogeneousQuotientEquiv I hI B hzero).finrank_eq,
    Module.finrank_directSum]

end PiExponentJets.W25

end

end OAI
