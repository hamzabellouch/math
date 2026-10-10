import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.Matrices

namespace OAI

/-! Expectations for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ}
namespace System
variable (s : System n (1:M))

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_projection (i : Fin n) : IsStarProjection (s.entry i i) := by
  exact ⟨by simp only [IsIdempotentElem,s.mul_entry,↓reduceIte],
    by exact s.star_entry i i⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma entry_absorb_left (i j : Fin n) : s.entry i i*s.entry i j=s.entry i j := by
  simp only [s.mul_entry,↓reduceIte]

omit [PartialOrder M] [StarOrderedRing M] in
lemma entry_absorb_right (i j : Fin n) : s.entry i j*s.entry j j=s.entry i j := by
  simp only [s.mul_entry,↓reduceIte]

omit [PartialOrder M] [StarOrderedRing M] in
lemma entry_norm_le (i j : Fin n) : ‖s.entry i j‖ ≤ 1 := by
  have hp := (s.diagonal_projection j).norm_le
  have he : star (s.entry i j)*s.entry i j=s.entry j j := by
    simp only [s.star_entry,s.mul_entry,↓reduceIte]
  rw [← he,CStarRing.norm_star_mul_self] at hp
  nlinarith [norm_nonneg (s.entry i j)]

def commutant : StarSubalgebra ℂ M where
  carrier := {a | ∀ i j, Commute a (s.entry i j)}
  zero_mem' := fun _ _ => Commute.zero_left _
  one_mem' := fun _ _ => Commute.one_left _
  add_mem' := fun ha hb i j => (ha i j).add_left (hb i j)
  mul_mem' := fun ha hb i j => (ha i j).mul_left (hb i j)
  algebraMap_mem' := fun c i j => Algebra.commutes c (s.entry i j)
  star_mem' := by
    intro a ha i j
    change star a*s.entry i j=s.entry i j*star a
    have h := congrArg star (ha j i).eq
    simpa only [star_mul,s.star_entry] using h.symm

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma mem_commutant (a : M) : a ∈ s.commutant ↔ ∀ i j, Commute a (s.entry i j) := Iff.rfl

def coordinate (x : M) (i j : Fin n) : M := ∑ k, s.entry k i*x*s.entry j k

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_commutes (x : M) (i j a b : Fin n) :
    Commute (s.coordinate x i j) (s.entry a b) := by
  classical
  change (∑ k, s.entry k i*x*s.entry j k)*s.entry a b =
    s.entry a b*(∑ k, s.entry k i*x*s.entry j k)
  simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc,s.mul_entry,mul_ite,mul_zero]
  simp only [← mul_assoc,s.mul_entry,ite_mul,zero_mul]
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma coordinate_mem (x : M) (i j : Fin n) : s.coordinate x i j ∈ s.commutant :=
  s.coordinate_commutes x i j

omit [PartialOrder M] [StarOrderedRing M] in
lemma reconstruct (x : M) : ∑ i, ∑ j, s.entry i j*s.coordinate x i j=x := by
  classical
  have hh (i j : Fin n) : s.entry i j*s.coordinate x i j = s.entry i i*x*s.entry j j := by
    simp [coordinate,Finset.mul_sum,← mul_assoc,s.mul_entry,ite_mul,zero_mul]
  simp_rw [hh]
  calc
    (∑ i, ∑ j, s.entry i i*x*s.entry j j) =
        (∑ i, s.entry i i)*x*(∑ j, s.entry j j) := by
          simp only [Finset.sum_mul,Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = x := by rw [s.sum_diag,one_mul,mul_one]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_in_commutant_is_central (b : M) (hb : b ∈ s.commutant)
    (hc : ∀ a ∈ s.commutant, Commute b a) (x : M) : Commute b x := by
  rw [← s.reconstruct x]
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact (hb i j).mul_right (hc _ (s.coordinate_mem x i j))

def sumExpect (x : M) : M := ∑ i, ∑ j, s.entry i j*x*s.entry j i

omit [PartialOrder M] [StarOrderedRing M] in
lemma sumExpect_commutes (x : M) (a b : Fin n) : Commute (s.sumExpect x) (s.entry a b) := by
  classical
  change (∑ i, ∑ j, s.entry i j*x*s.entry j i)*s.entry a b =
    s.entry a b*(∑ i, ∑ j, s.entry i j*x*s.entry j i)
  simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc,s.mul_entry,mul_ite,mul_zero]
  simp only [← mul_assoc,s.mul_entry,ite_mul,zero_mul]
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma sumExpect_of_commutes (x : M) (hx : x ∈ s.commutant) :
    s.sumExpect x=(n : ℕ) • x := by
  classical
  calc
    s.sumExpect x = ∑ i, ∑ j, x*(s.entry i j*s.entry j i) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [← mul_assoc,← (hx i j).eq]
    _ = ∑ i, ∑ j : Fin n, x*s.entry i i := by simp only [s.mul_entry,↓reduceIte]
    _ = (n : ℕ) • x := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Finset.smul_sum,
        ← Finset.mul_sum,s.sum_diag,mul_one]

omit [PartialOrder M] [StarOrderedRing M] in
lemma sumExpect_star (x : M) : s.sumExpect (star x)=star (s.sumExpect x) := by
  simp only [sumExpect,star_sum,star_mul,s.star_entry,mul_assoc]

def expect (x : M) : M := (n : ℝ)⁻¹ • s.sumExpect x

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_mem (x : M) : s.expect x ∈ s.commutant := by
  intro a b
  exact (s.sumExpect_commutes x a b).smul_left _

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_fix (hn : 0 < n) (x : M) (hx : x ∈ s.commutant) : s.expect x=x := by
  rw [expect,s.sumExpect_of_commutes x hx,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hn),one_smul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_idempotent (hn : 0 < n) (x : M) : s.expect (s.expect x)=s.expect x :=
  s.expect_fix hn _ (s.expect_mem x)

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_one (hn : 0 < n) : s.expect 1=1 := s.expect_fix hn 1 s.commutant.one_mem

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_add (x y : M) : s.expect (x+y)=s.expect x+s.expect y := by
  simp only [expect,sumExpect,mul_add,add_mul,Finset.sum_add_distrib,smul_add]

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_smul (c : ℂ) (x : M) : s.expect (c • x)=c • s.expect x := by
  simp only [expect,sumExpect,mul_smul_comm,smul_mul_assoc,← Finset.smul_sum]
  exact smul_comm _ _ _

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_star (x : M) : s.expect (star x)=star (s.expect x) := by
  simp only [expect,s.sumExpect_star,star_smul,star_trivial]

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_bimodule (a b x : M) (ha : a ∈ s.commutant) (hb : b ∈ s.commutant) :
    s.expect (a*x*b)=a*s.expect x*b := by
  simp only [expect,mul_smul_comm,smul_mul_assoc]
  congr 1
  simp only [sumExpect,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  calc
    s.entry i j*(a*x*b)*s.entry j i = a*s.entry i j*x*(b*s.entry j i) := by
      simp only [← mul_assoc]
      rw [← (ha i j).eq]
    _ = a*(s.entry i j*x*s.entry j i)*b := by rw [(hb j i).eq]; simp only [mul_assoc]

omit [StarOrderedRing M] in
lemma trace_sumExpect (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (x : M) :
    τ (s.sumExpect x)=(n : ℕ) • τ x := by
  classical
  calc
    τ (s.sumExpect x) = ∑ i : Fin n, ∑ j, τ (s.entry j j*x) := by
      simp only [sumExpect,map_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [htr,← mul_assoc,s.mul_entry,ite_eq_left rfl]
    _ = (n : ℕ) • τ x := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,← map_sum,← Finset.sum_mul,s.sum_diag,one_mul]

omit [StarOrderedRing M] in
lemma trace_expect (hn : 0 < n) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (x : M) : τ (s.expect x)=τ x := by
  rw [expect,← Complex.coe_smul,map_smul,s.trace_sumExpect τ htr x,
    ← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have hn0 : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast,inv_mul_cancel₀ hn0,one_smul]

end System
end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_zero : s.expect 0=0 := by simp [expect,sumExpect]
omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_sub (x y : M) : s.expect (x-y)=s.expect x-s.expect y := by
  simp only [expect,sumExpect,mul_sub,sub_mul,Finset.sum_sub_distrib,smul_sub]

include htr
omit [StarOrderedRing M] in
lemma expect_pairing (hn : 0 < n) (x a : M) (ha : a ∈ s.commutant) :
    τ (star a*s.expect x)=τ (star a*x) := by
  have he := s.expect_bimodule (star a) 1 x (s.commutant.star_mem' ha) s.commutant.one_mem
  simp only [mul_one] at he
  rw [← he,s.trace_expect hn τ htr]

lemma expect_orthogonal (hn : 0 < n) (x : M) :
    inner ℂ (τ.toPreGNS (s.expect x)) (τ.toPreGNS (x-s.expect x))=0 := by
  rw [PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,mul_sub,map_sub]
  rw [s.expect_pairing τ htr hn x _ (s.expect_mem x),sub_self]

lemma expect_pythagoras (hn : 0 < n) (x : M) :
    ‖τ.toPreGNS x‖^2 = ‖τ.toPreGNS (s.expect x)‖^2 + ‖τ.toPreGNS (x-s.expect x)‖^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (τ.toPreGNS (s.expect x)) (τ.toPreGNS (x-s.expect x)) (s.expect_orthogonal τ htr hn x)
  simpa only [← map_add,add_sub_cancel,pow_two] using h

lemma expect_norm_le (hn : 0 < n) (x : M) : ‖τ.toPreGNS (s.expect x)‖ ≤ ‖τ.toPreGNS x‖ := by
  have h := s.expect_pythagoras τ htr hn x
  nlinarith [sq_nonneg ‖τ.toPreGNS (x-s.expect x)‖,norm_nonneg (τ.toPreGNS x),
    norm_nonneg (τ.toPreGNS (s.expect x))]

lemma commutator_norm_le_residual (x p : M) (hp : IsStarProjection p)
    (hc : Commute (s.expect x) p) :
    ‖τ.toPreGNS (x*p-p*x)‖ ≤ 2*‖τ.toPreGNS (x-s.expect x)‖ := by
  have he : x*p-p*x=(x-s.expect x)*p-p*(x-s.expect x) := by
    simp only [sub_mul,mul_sub,hc.eq]; abel
  rw [he,map_sub]
  calc
    ‖τ.toPreGNS ((x-s.expect x)*p)-τ.toPreGNS (p*(x-s.expect x))‖ ≤
        ‖τ.toPreGNS ((x-s.expect x)*p)‖+‖τ.toPreGNS (p*(x-s.expect x))‖ := norm_sub_le _ _
    _ ≤ ‖p‖*‖τ.toPreGNS (x-s.expect x)‖+‖p‖*‖τ.toPreGNS (x-s.expect x)‖ :=
      add_le_add (preGNS_norm_mul_right_le τ htr _ _) (preGNS_norm_mul_le τ _ _)
    _ ≤ 2*‖τ.toPreGNS (x-s.expect x)‖ := by nlinarith [hp.norm_le,norm_nonneg (τ.toPreGNS (x-s.expect x))]

lemma energy_drop (hn : 0 < n) (x p : M) (hp : IsStarProjection p)
    (hc : Commute (s.expect x) p) :
    ‖τ.toPreGNS (s.expect x)‖^2 ≤ ‖τ.toPreGNS x‖^2 -
      ‖τ.toPreGNS (x*p-p*x)‖^2/4 := by
  have h := s.commutator_norm_le_residual τ htr x p hp hc
  have hh := s.expect_pythagoras τ htr hn x
  nlinarith [norm_nonneg (τ.toPreGNS (x*p-p*x)),norm_nonneg (τ.toPreGNS (x-s.expect x))]
end PopaMatrices.System

end

end OAI
