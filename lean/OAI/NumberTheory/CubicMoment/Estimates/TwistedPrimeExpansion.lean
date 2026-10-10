import OAI.NumberTheory.CubicMoment.Estimates.TwistedShortProducts
import OAI.NumberTheory.CubicMoment.Estimates.ComplexWeightedConvolution
import OAI.NumberTheory.CubicMoment.Estimates.PrimeWeightExpansion

namespace OAI

/-! Exact short inversion with independent residue and norm twists on every
original von Mangoldt factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma twisted_short_series_expansion (F : ℝ) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) :
    (∏ i, twistArithmetic (q i) (η i) (t i) (shortVonMangoldt F)) =
      ∑ S : Finset ι, MvPowerSeries.C (shortBranchScalar S)*
        ∏ j : shortBranchIndex S,
          twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor F S j) := by
  simp_rw [shortVonMangoldt_two_four,twistArithmetic_sub,twistArithmetic_two]
  rw [Finset.prod_sub,Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  rw [twisted_branch_product]
  have hp : (∏ i ∈ Finset.univ\S, 2*twistArithmetic (q i) (η i) (t i) (shortTwoFactor F)) =
      (2 : MvPowerSeries EisensteinIdealPrime ℂ)^(Fintype.card ι-S.card)*
        ∏ i ∈ Finset.univ\S, twistArithmetic (q i) (η i) (t i) (shortTwoFactor F) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ]
  rw [hp]
  simp only [shortBranchScalar,map_mul,map_pow,map_neg,map_one,map_ofNat]
  ring

theorem twisted_prime_coeff_expansion {F : ℝ} (hF : 0 ≤ F)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ i, twistArithmetic (q i) (η i) (t i) idealVonMangoldt) =
      ∑ S : Finset ι, shortBranchScalar S * MvPowerSeries.coeff ν
        (∏ j : shortBranchIndex S,
          twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor F S j)) := by
  rw [twisted_short_product_coeff hF q η t ν hν,
    twisted_short_series_expansion F q η t,map_sum]
  simp only [MvPowerSeries.coeff_C_mul]

theorem primaryTwistedPrimeWeight_expansion (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) :
    primaryComplexProductPolynomial (fun i => twistArithmetic (q i) (η i) (t i) idealVonMangoldt) χ V Y =
      ∑ S : Finset ι, shortBranchScalar S * primaryComplexProductPolynomial
        (fun j : shortBranchIndex S =>
          twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
            (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j)) χ V Y := by
  unfold primaryComplexProductPolynomial
  calc
    _ = ∑ b ∈ primaryElementBall (2*Y), ∑ S : Finset ι, shortBranchScalar S *
        MvPowerSeries.coeff (idealExponentOf b)
          (∏ j : shortBranchIndex S,
            twistArithmetic (q (shortBranchSource S j)) (η (shortBranchSource S j))
              (t (shortBranchSource S j)) (shortBranchFactor (2*Y) S j))*χ b*V (norm b/Y) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := mem_primaryElementBall.mp hb
      have hN : idealExponentNorm (idealExponentOf b) ≤ 2*Y := by
        simpa only [idealExponentOf_norm (primary_ne_zero hb'.1)] using hb'.2
      rw [twisted_prime_coeff_expansion (by positivity : 0 ≤ 2*Y) q η t _ hN,
        Finset.sum_mul,Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end CubicFirstMoment

end

end OAI
