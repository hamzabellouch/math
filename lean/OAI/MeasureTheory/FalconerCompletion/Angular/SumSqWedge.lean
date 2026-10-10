import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAxisIntegral

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma sum_sq_wedgeND {ι : Type*} [Fintype ι] (X E : ι → ℝ) :
    (∑ i, ∑ j, (X i*E j-X j*E i)^2) =
      2*((∑ i, X i^2)*(∑ j, E j^2) - (∑ i, X i*E i)^2) := by
  have ht (i j) : (X i*E j-X j*E i)^2 =
      X i^2*E j^2 + E i^2*X j^2 - (2*(X i*E i))*(X j*E j) := by ring
  simp_rw [ht,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,← Finset.mul_sum]
  ring

lemma angularGeneratorND_sum_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (x e : V) :
    (∑ i, ∑ j, (inner ℝ (angularGeneratorND (b i) (b j) x) e)^2) =
      2*(‖x‖^2*‖e‖^2-(inner ℝ x e)^2) := by
  simp_rw [angularGeneratorND_apply,inner_sub_left,real_inner_smul_left]
  rw [sum_sq_wedgeND,b.sum_sq_inner_right x,b.sum_sq_inner_right e]
  congr 2
  have h : ∑ i, inner ℝ (b i) x * inner ℝ (b i) e = inner ℝ x e := by
    simpa only [real_inner_comm (b _) x] using b.sum_inner_mul_inner x e
  rw [h]

lemma angularGeneratorND_sum_second {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (x e : V) :
    (∑ i, ∑ j, inner ℝ (angularGeneratorND (b i) (b j)
      (angularGeneratorND (b i) (b j) x)) e) =
      -(2*((Fintype.card ι:ℝ)-1))*inner ℝ x e := by
  classical
  simp_rw [angularGeneratorND_apply,inner_sub_left,real_inner_smul_left,
    inner_sub_right,inner_smul_right,b.inner_eq_ite]
  have ht (i j : ι) :
      (inner ℝ (b i) x * (if i = j then (1:ℝ) else 0) - inner ℝ (b j) x * 1) * inner ℝ (b j) e -
        (inner ℝ (b i) x * 1 - inner ℝ (b j) x * (if j = i then (1:ℝ) else 0)) * inner ℝ (b i) e =
      (if i=j then 2*inner ℝ (b i) x*inner ℝ (b i) e else 0) -
        inner ℝ (b j) x*inner ℝ (b j) e - inner ℝ (b i) x*inner ℝ (b i) e := by
    by_cases h : i = j
    · subst j; simp; ring
    · simp [h,Ne.symm h]
  simp only [ite_true]
  simp_rw [ht,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  have h : ∑ i, inner ℝ (b i) x * inner ℝ (b i) e = inner ℝ x e := by
    simpa only [real_inner_comm (b _) x] using b.sum_inner_mul_inner x e
  simp_rw [mul_assoc,← Finset.mul_sum,h]
  ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
