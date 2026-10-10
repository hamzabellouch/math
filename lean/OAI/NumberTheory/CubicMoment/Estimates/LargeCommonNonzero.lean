import OAI.NumberTheory.CubicMoment.Estimates.CommonNonzeroBound

namespace OAI

/-! The genuine large-common-factor part of an arbitrary squarefree
Gram form. Its coefficient loss is the proved divisor energy bound. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem large_common_nonzero_bound {ε ζ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hζ : 0 < ζ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C E : ℝ, 0 < C ∧ 0 < E ∧ ∀ (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (A N D : ℝ), 0 < A → 1 ≤ N → 1 ≤ D →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ N ≤ norm a ∧ norm a ≤ 2*N) →
      ‖∑ k ∈ (commonRowFactors S).filter (fun k => D ≤ norm k),
        (commonGramBlock S v W A k-commonGramZeroMode S v W A k)‖ ≤
      commonNonzeroCost C ε 2 1 A N D * (E*(2*N)^ζ*∑ a ∈ S, ‖v a‖^2) := by
  obtain ⟨C,hC,hblock⟩ := commonGramBlock_outer_nonzero hε hε₁ (by norm_num : (1:ℝ) ≤ 2) W hW hW'
  obtain ⟨E,hE,henergy⟩ := common_energy_small_power ζ hζ
  refine ⟨C,E,hC,hE,?_⟩
  intro S v A N D hA hN hD hS
  have hcost : 0 ≤ commonNonzeroCost C ε 2 1 A N D :=
    commonNonzeroCost_nonneg hC.le (by norm_num) hA.le (zero_le_one.trans hN)
  have hb (k : Eisenstein) (hk : k ∈ (commonRowFactors S).filter (fun k => D ≤ norm k)) :
      ‖(commonGramBlock S v W A k-commonGramZeroMode S v W A k)‖ ≤ commonNonzeroCost C ε 2 1 A N D *
        ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S v k) := by
    have hh := hblock S v 1 A N D (by norm_num) hA hN hD hS k
      (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
    simpa only [one_pow,div_one,mul_assoc,mul_comm,mul_left_comm] using hh
  calc
    _ ≤ ∑ k ∈ (commonRowFactors S).filter (fun k => D ≤ norm k),
        commonNonzeroCost C ε 2 1 A N D *
          ((2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S v k) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
    _ = commonNonzeroCost C ε 2 1 A N D *
        (∑ k ∈ (commonRowFactors S).filter (fun k => D ≤ norm k),
          (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S v k) := by rw [Finset.mul_sum]
    _ ≤ commonNonzeroCost C ε 2 1 A N D *
        (∑ k ∈ commonRowFactors S, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S v k) := by
      apply mul_le_mul_of_nonneg_left _ hcost
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro k hk _
      unfold commonBlockEnergy
      positivity
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (henergy S v (2*N) (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1,(hS a ha).2.2.2⟩)) hcost

end CubicFirstMoment

end

end OAI
