import OAI.NumberTheory.CubicMoment.Estimates.ShortMoebiusProducts
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorMoments

namespace OAI

/-! Each term of the short Möbius product expansion is an actual finite
family of the three permitted arithmetic factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev shortBranchIndex (S : Finset ι) := (↥S × Fin 4) ⊕ (↥(Finset.univ\S) × Fin 2)

instance shortBranchIndex_fintype (S : Finset ι) : Fintype (shortBranchIndex S) :=
  inferInstanceAs (Fintype ((↥S × Fin 4) ⊕ (↥(Finset.univ\S) × Fin 2)))

instance shortBranchIndex_decidableEq (S : Finset ι) : DecidableEq (shortBranchIndex S) :=
  inferInstanceAs (DecidableEq ((↥S × Fin 4) ⊕ (↥(Finset.univ\S) × Fin 2)))

def shortBranchFactor (F : ℝ) (S : Finset ι) : shortBranchIndex S → EisensteinArithmeticFunction
  | Sum.inl (_,j) => ![shortIdealMoebius F,shortIdealMoebius F,idealZeta,idealLogNorm] j
  | Sum.inr (_,j) => ![shortIdealMoebius F,idealLogNorm] j

lemma shortBranchFactor_spec (F : ℝ) (S : Finset ι) (i : shortBranchIndex S) :
    ShortArithmeticFactor F (shortBranchFactor F S i) := by
  rcases i with ⟨i,j⟩ | ⟨i,j⟩
  · fin_cases j <;> simp [shortBranchFactor,ShortArithmeticFactor]
  · fin_cases j <;> simp [shortBranchFactor,ShortArithmeticFactor]

lemma shortBranchFactor_product (F : ℝ) (S : Finset ι) :
    (∏ i, shortBranchFactor F S i) =
      (∏ _i ∈ S, shortFourFactor F)*(∏ _i ∈ Finset.univ\S, shortTwoFactor F) := by
  change (∏ i : (↥S × Fin 4) ⊕ (↥(Finset.univ\S) × Fin 2), shortBranchFactor F S i) = _
  rw [Fintype.prod_sum_type,Fintype.prod_prod_type,Fintype.prod_prod_type]
  simp [shortBranchFactor,Fin.prod_univ_four,Fin.prod_univ_two,
    shortFourFactor,shortTwoFactor]

/-- Explicit finite short-factor expansion on each primary norm ball. -/
theorem short_prime_product_expansion {F : ℝ} (hF : 0 ≤ F)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν (∏ _i : ι, idealVonMangoldt) =
      ∑ S ∈ (Finset.univ : Finset ι).powerset,
        (-1 : ℝ)^S.card * 2^(Fintype.card ι-S.card) *
          MvPowerSeries.coeff ν (∏ i, shortBranchFactor F S i) := by
  rw [shortVonMangoldt_product_expansion (ι := ι) hF ν hν,map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  rw [shortBranchFactor_product]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_sdiff_of_subset hsub,Finset.card_univ]
  have he : (-1 : EisensteinArithmeticFunction)^S.card *
        (shortFourFactor F)^S.card *
          (2^(Fintype.card ι-S.card)*(shortTwoFactor F)^(Fintype.card ι-S.card)) =
      MvPowerSeries.C ((-1:ℝ)^S.card*2^(Fintype.card ι-S.card)) *
        ((shortFourFactor F)^S.card*(shortTwoFactor F)^(Fintype.card ι-S.card)) := by
    simp only [map_mul,map_pow,map_neg,map_one,map_ofNat]
    ring
  rw [he,MvPowerSeries.coeff_C_mul]

end CubicFirstMoment

end

end OAI
