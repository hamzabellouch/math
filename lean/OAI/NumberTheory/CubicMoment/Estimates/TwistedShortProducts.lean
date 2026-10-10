import OAI.NumberTheory.CubicMoment.Estimates.ArithmeticTwist
import OAI.NumberTheory.CubicMoment.Estimates.ShortConvolutionExpansion

namespace OAI

/-! Short inversion with a different residue character and Mellin height
on each original prime factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma twistArithmetic_two (q : Eisenstein) (η : MulChar (Residues q) ℂ) (t : ℝ)
    (A : EisensteinArithmeticFunction) :
    twistArithmetic q η t (2*A) = 2*twistArithmetic q η t A := by
  rw [two_mul,twistArithmetic_add,two_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem twisted_short_product_coeff {F : ℝ} (hF : 0 ≤ F)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ i, twistArithmetic (q i) (η i) (t i) idealVonMangoldt) =
      MvPowerSeries.coeff ν (∏ i, twistArithmetic (q i) (η i) (t i) (shortVonMangoldt F)) := by
  have h : ∀ S : Finset ι, ∀ κ : EisensteinIdealExponent, idealExponentNorm κ ≤ F →
      MvPowerSeries.coeff κ (∏ i ∈ S, twistArithmetic (q i) (η i) (t i) idealVonMangoldt) =
      MvPowerSeries.coeff κ (∏ i ∈ S, twistArithmetic (q i) (η i) (t i) (shortVonMangoldt F)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intros; rfl
    | @insert i S hi ih =>
      intro κ hκ
      rw [Finset.prod_insert hi,Finset.prod_insert hi,MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have h₁ : p.1 ≤ κ := by rw [← he]; exact le_add_of_nonneg_right zero_le
      have h₂ : p.2 ≤ κ := by rw [← he]; exact le_add_of_nonneg_left zero_le
      rw [ih p.2 ((idealExponentNorm_mono h₂).trans hκ)]
      congr 1
      change ((MvPowerSeries.coeff p.1 idealVonMangoldt:ℝ):ℂ)*residueNormTwist (q i) (η i) (t i) p.1 =
        ((MvPowerSeries.coeff p.1 (shortVonMangoldt F):ℝ):ℂ)*residueNormTwist (q i) (η i) (t i) p.1
      rw [shortVonMangoldt_local hF p.1 ((idealExponentNorm_mono h₁).trans hκ)]
  exact h Finset.univ ν hν

def shortBranchSource (S : Finset ι) : shortBranchIndex S → ι
  | Sum.inl (i,_) => i
  | Sum.inr (i,_) => i

lemma twisted_branch_product (F : ℝ) (S : Finset ι) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) :
    (∏ j : shortBranchIndex S,
      twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
        (t (shortBranchSource S j)) (shortBranchFactor F S j)) =
      (∏ i ∈ S, twistArithmetic (q i) (η i) (t i) (shortFourFactor F))*
        ∏ i ∈ Finset.univ\S, twistArithmetic (q i) (η i) (t i) (shortTwoFactor F) := by
  rw [Fintype.prod_sum_type,Fintype.prod_prod_type,Fintype.prod_prod_type]
  simp only [shortBranchSource,shortBranchFactor,Fin.prod_univ_four,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  simp only [← twistArithmetic_mul]
  change (∏ x : S, twistArithmetic (q x) (η x) (t x) (shortFourFactor F))*
    (∏ x : ↥(Finset.univ\S), twistArithmetic (q x) (η x) (t x) (shortTwoFactor F)) = _
  rw [Finset.prod_coe_sort (s := S) (f := fun i => twistArithmetic (q i) (η i) (t i) (shortFourFactor F)),
    Finset.prod_coe_sort (s := Finset.univ\S) (f := fun i => twistArithmetic (q i) (η i) (t i) (shortTwoFactor F))]

end CubicFirstMoment

end

end OAI
