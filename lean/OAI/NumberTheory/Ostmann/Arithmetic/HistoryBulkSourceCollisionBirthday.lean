import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionErrorBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullDisintegration

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkSourceCollisionBirthday
open Construction Characters Characters.Template.OneSidedPhase GiantCollisionError
attribute [local instance] Classical.propDecidable

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
private theorem productPrior_mean_update_two (μ : ι→FinitePrior Ω) (i j : ι)
    (F : (ι→Ω)→ℝ) :
    (productPrior μ).mean F=(productPrior μ).mean (fun x=>
      (μ i).mean (fun p=>(μ j).mean (fun q=>F (Function.update (Function.update x i p) j q)))) := by
  apply Complex.ofReal_injective
  simpa only [FinitePrior.mean,FinitePrior.cmean,Complex.ofReal_sum,Complex.ofReal_mul] using
    productPrior_cmean_update_two μ i j (fun x=>(F x:ℂ))

theorem productPrior_coordinate_collision (μ : FinitePrior Ω) (i j : ι) (hij : i≠j) :
    (productPrior (fun _ : ι=>μ)).mean (fun x=>if x i=x j then 1 else 0)=
      (μ.pair μ).mean (fun z=>if z.1=z.2 then 1 else 0) := by
  rw [productPrior_mean_update_two (fun _ : ι=>μ) i j]
  simp only [Function.update_of_ne hij,Function.update_self,FinitePrior.mean_const]
  simp only [FinitePrior.mean,FinitePrior.pair,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem productPrior_noninjective_mass_le (μ : FinitePrior Ω) (B : ℝ)
    (hB : ∀a,μ.mass a ≤ B) :
    (productPrior (fun _ : ι=>μ)).mean (fun x=>if ¬Function.Injective x then 1 else 0) ≤
      (Fintype.card ι:ℝ)^2*B := by
  have hB0 : 0 ≤ B := calc
    0 ≤ μ.mean μ.mass := μ.mean_nonneg μ.mass_nonneg
    _ ≤ μ.mean (fun _=>B) := μ.mean_mono hB
    _ = B := μ.mean_const B
  let ν := productPrior (fun _ : ι=>μ)
  have hpoint (x : ι→Ω) : (if ¬Function.Injective x then (1:ℝ) else 0) ≤
      ∑i:ι,∑j:ι,if i≠j ∧ x i=x j then 1 else 0 := by
    by_cases hx : Function.Injective x
    · simp only [hx,not_true_eq_false,ite_false]
      exact Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>by positivity))
    · rw [ite_eq_left hx]
      obtain ⟨i,j,he,hne⟩ := Function.not_injective_iff.mp hx
      have hlocal : (1:ℝ) ≤ ∑j':ι,if i≠j' ∧ x i=x j' then 1 else 0 := by
        have hh := Finset.single_le_sum
          (f:=fun j':ι=>if i≠j' ∧ x i=x j' then (1:ℝ) else 0)
          (fun _ _=>by positivity) (Finset.mem_univ j)
        simpa [hne,he] using hh
      exact hlocal.trans (Finset.single_le_sum
        (f:=fun i':ι=>∑j':ι,if i'≠j' ∧ x i'=x j' then (1:ℝ) else 0)
        (fun _ _=>Finset.sum_nonneg (fun _ _=>by positivity)) (Finset.mem_univ i))
  calc
    _ ≤ ν.mean (fun x=>∑i:ι,∑j:ι,if i≠j ∧ x i=x j then 1 else 0) := ν.mean_mono hpoint
    _ = ∑i:ι,∑j:ι,ν.mean (fun x=>if i≠j ∧ x i=x j then 1 else 0) := by
      simp only [FinitePrior.mean,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ ≤ ∑i:ι,∑j:ι,B := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i=j
      · subst j
        simpa only [ne_eq,not_true_eq_false,false_and,ite_false,FinitePrior.mean_const] using hB0
      · simpa only [ne_eq,hij,not_false_eq_true,true_and] using
          (productPrior_coordinate_collision μ i j hij).le.trans (equality_mass_le μ μ B hB)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

theorem primeSource_noninjective_mass_le (S : PrimeSource) (B : ℝ)
    (hB : ∀p,S.law.mass p ≤ B) :
    (dependentProductPrior (fun _ : ι=>S.law)).mean
      (fun x=>if ¬Function.Injective (fun i=>(x i).val) then 1 else 0) ≤
        (Fintype.card ι:ℝ)^2*B := by
  have he (x : ι→S.Sample) : Function.Injective (fun i=>(x i).val) ↔ Function.Injective x :=
    ⟨fun h i j hij=>h (congrArg Subtype.val hij),fun h i j hij=>h (Subtype.ext hij)⟩
  simp only [he]
  exact productPrior_noninjective_mass_le S.law B hB

theorem primeSource_guard_error (S : PrimeSource) (B : ℝ)
    (hB : ∀p,S.law.mass p ≤ B) (f g : (ι→S.Sample)→ℂ) {A : ℝ} (hA : 0 ≤ A)
    (heq : ∀x,Function.Injective (fun i=>(x i).val) → f x=g x)
    (hbound : ∀x,¬Function.Injective (fun i=>(x i).val) → ‖f x-g x‖ ≤ A) :
    ‖(dependentProductPrior (fun _ : ι=>S.law)).cmean f-
      (dependentProductPrior (fun _ : ι=>S.law)).cmean g‖ ≤
        A*((Fintype.card ι:ℝ)^2*B) := by
  exact (cmean_error_of_agree_off (dependentProductPrior (fun _ : ι=>S.law))
    (fun x=>¬Function.Injective (fun i=>(x i).val)) f g A
    (fun x hx=>heq x (not_not.mp hx)) hbound).trans
      (mul_le_mul_of_nonneg_left (primeSource_noninjective_mass_le S B hB) hA)

end Ostmann.Arithmetic.HistoryBulkSourceCollisionBirthday

end

end OAI
