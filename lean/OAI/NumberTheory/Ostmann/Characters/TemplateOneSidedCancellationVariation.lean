import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationDegree
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationProfiles

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory TemplateSupportRemoval Template Arithmetic
variable {ι σ τ : Type*} [DecidableEq ι] [Fintype σ] [Fintype τ]

def leafDegreeBudget (k : ℕ) (g : σ → Guard ι) (leaf : τ → BottomExpression (ι:=ι) k)
    (X A B : ℝ) : ℕ :=
  2*((∑ s, (profileGuards g (fun t => periodExpression k (leaf t).2.2) X A B s).expression.degreeBudget)+
    ∑ t, (periodExpression k (leaf t).2.2).degreeBudget)+1

theorem leafData_degreeCost_le (k : ℕ) (g : σ → Guard ι) (leaf : τ → BottomExpression (ι:=ι) k)
    (i : ι) (x : Other i → ℤ) (X A B : ℝ) :
    (leafData k g leaf i x X A B).degreeCost ≤ leafDegreeBudget k g leaf X A B := by
  apply Nat.add_le_add_right _ 1
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro s hs
    change (-((profileGuards g (fun t => periodExpression k (leaf t).2.2) X A B s).polynomial i x)).natDegree ≤ _
    rw [Polynomial.natDegree_neg]
    exact guard_degree_le _ _ _
  · apply Finset.sum_le_sum
    intro t ht
    exact (Nat.sub_le _ _).trans (argument_degree_le _ _ _)

theorem leafData_progressionVariation_le (k : ℕ) (g : σ → Guard ι)
    (leaf : τ → BottomExpression (ι:=ι) k) (i : ι) (x : Other i → ℤ)
    {X A B : ℝ} (hX : 0 < X) (hAB : A ≤ B)
    (hg : ∀ s, (g s).expression.Valid)
    (he : ∀ t, (periodExpression k (leaf t).2.2).Valid) (ρ : 𝓢(ℝ,ℂ)) (Q a N : ℕ) :
    progressionVariation
      (fun n => (leafData k g leaf i x X A B).weight ρ ((Q*n+a : ℕ):ℝ)) N ≤
    (leafDegreeBudget k g leaf X A B : ℝ)*
      ((Real.exp (B/2)*leafProfileBound ρ)^(Fintype.card τ)*
        (3+(Fintype.card τ:ℝ)*(B-A))) := by
  have hh := (leafData k g leaf i x X A B).progressionVariation_le ρ
    (leafData_ranges k g leaf i x hX hAB hg he ρ) Q a N
  apply hh.trans
  unfold HistoryPolynomialData.variationCost
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast leafData_degreeCost_le k g leaf i x X A B
  · exact mul_nonneg (pow_nonneg (mul_nonneg (Real.exp_pos _).le (leafProfileBound_pos ρ).le) _)
      (add_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hAB)))

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
