import Mathlib

namespace OAI

noncomputable section

namespace KKProjectionSupport

noncomputable section

open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A]

def partitionLinear (p : ι → A) : (ι → ℂ) →ₗ[ℂ] A where
  toFun c := ∑ i, c i • p i
  map_add' c d := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c d := by simp only [Pi.smul_apply,smul_smul,Finset.smul_sum]; rfl

omit [DecidableEq ι] in
@[simp] theorem partitionLinear_apply (p : ι → A) (c : ι → ℂ) :
    partitionLinear p c=∑ i, c i • p i := rfl

theorem partitionLinear_mul (p : ι → A)
    (hp : ∀ i j, p i*p j=if i=j then p i else 0) (c d : ι → ℂ) :
    partitionLinear p (c*d)=partitionLinear p c*partitionLinear p d := by
  symm
  calc
    partitionLinear p c*partitionLinear p d = ∑ i, ∑ j, (c i*d j) • (p i*p j) := by
      simp only [partitionLinear_apply]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm]
    _ = partitionLinear p (c*d) := by
      simp only [hp,smul_ite,smul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
        partitionLinear_apply,Pi.mul_apply]

variable [StarRing A] [StarModule ℂ A]

def partitionHom (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hort : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1) : (ι → ℂ) →⋆ₐ[ℂ] A where
  toFun := partitionLinear p
  map_zero' := (partitionLinear p).map_zero
  map_one' := by simpa only [partitionLinear_apply,Pi.one_apply,one_smul] using h1
  map_add' := (partitionLinear p).map_add
  map_mul' := partitionLinear_mul p (fun i j => by
    split_ifs with h
    · subst j; exact (hp i).isIdempotentElem.eq
    · exact hort i j h)
  commutes' c := by simp only [Algebra.algebraMap_eq_smul_one,map_smul,
    partitionLinear_apply,Pi.one_apply,one_smul,h1]
  map_star' c := by simp only [partitionLinear_apply,star_sum,star_smul,Pi.star_apply,
    fun i => (hp i).isSelfAdjoint.star_eq]

@[simp] theorem partitionHom_apply (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hort : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1) (c : ι → ℂ) :
    partitionHom p hp hort h1 c=∑ i, c i • p i := rfl

@[simp] theorem partitionHom_pow (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (hort : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1) (c : ι → ℂ) (k : ℕ) :
    (partitionHom p hp hort h1 c)^k=∑ i, (c i)^k • p i := by
  rw [← map_pow]; rfl

end

end KKProjectionSupport
end

end OAI
