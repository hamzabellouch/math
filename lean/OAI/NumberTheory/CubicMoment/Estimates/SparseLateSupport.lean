import OAI.NumberTheory.CubicMoment.Estimates.SparseDivisorRankin
import OAI.NumberTheory.CubicMoment.Estimates.ModelOverlapCounting

namespace OAI

/-! A literal sparse-support count: primary numbers containing a large
squarefree divisor made from small primes occupy a power-saving fraction
of a norm ball. The multiple count is the proved Eisenstein lattice bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def sparseLateSupport (X C η B : ℝ) : Finset Eisenstein :=
  (primaryElementBall B).filter (fun b => ∃ d : Eisenstein,
    primary d ∧ Squarefree d ∧ d ∣ b ∧ X^η ≤ norm d ∧
      ∀ p ∈ primaryPrimeFactors d, norm p ≤ (Real.log X)^C)

lemma divisible_union_card (S D : Finset Eisenstein) {B : ℝ}
    (hB : 0 ≤ B) (hS : ∀ b ∈ S, b ≠ 0 ∧ norm b ≤ B)
    (hD : ∀ d ∈ D, d ≠ 0) (hcover : ∀ b ∈ S, ∃ d ∈ D, d ∣ b) :
    (S.card:ℝ) ≤ 18*B*(∑ d ∈ D, (norm d)⁻¹) := by
  have hsub : S ⊆ D.biUnion (fun d => S.filter (fun b => d ∣ b)) := by
    intro b hb
    obtain ⟨d,hd,hdiv⟩ := hcover b hb
    exact Finset.mem_biUnion.mpr ⟨d,hd,Finset.mem_filter.mpr ⟨hb,hdiv⟩⟩
  calc
    _ ≤ ∑ d ∈ D, ((S.filter (fun b => d ∣ b)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ d ∈ D, 18*B/norm d := Finset.sum_le_sum
      (fun d hd => divisible_row_card_le S hB hS d (hD d hd))
    _ = _ := by simp only [Finset.mul_sum,div_eq_mul_inv]

theorem sparseLateSupport_card_saving (hpnt : PrimaryPrimePNT)
    {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      ∀ B : ℝ, 0 ≤ B → ((sparseLateSupport X C η B).card:ℝ) ≤ 18*B*X^(-δ) := by
  obtain ⟨δ,hδ,hbound⟩ := polylog_smooth_divisor_reciprocal_saving hpnt hC hη
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hbound] with X hX
  intro B hB
  let S := sparseLateSupport X C η B
  let D := (primaryElementBall B).filter (fun d => Squarefree d ∧ X^η ≤ norm d ∧
    ∀ p ∈ primaryPrimeFactors d, norm p ≤ (Real.log X)^C)
  have hS : ∀ b ∈ S, b ≠ 0 ∧ norm b ≤ B := by
    intro b hb
    have hh := mem_primaryElementBall.mp (Finset.mem_filter.mp hb).1
    exact ⟨primary_ne_zero hh.1,hh.2⟩
  have hD : ∀ d ∈ D, primary d ∧ Squarefree d := by
    intro d hd
    exact ⟨(mem_primaryElementBall.mp (Finset.mem_filter.mp hd).1).1,
      (Finset.mem_filter.mp hd).2.1⟩
  have hcover : ∀ b ∈ S, ∃ d ∈ D, d ∣ b := by
    intro b hb
    obtain ⟨_,d,hd,hsd,hdiv,hsize,hsmooth⟩ := Finset.mem_filter.mp hb
    refine ⟨d,Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hd,?_⟩,
      hsd,hsize,hsmooth⟩,hdiv⟩
    exact (norm_le_of_dvd (hS b hb).1 hdiv).trans (hS b hb).2
  apply (divisible_union_card S D hB hS (fun d hd => primary_ne_zero (hD d hd).1) hcover).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hX D hD (fun d hd => (Finset.mem_filter.mp hd).2.2.1)
    (fun d hd => (Finset.mem_filter.mp hd).2.2.2)

end CubicFirstMoment

end

end OAI
