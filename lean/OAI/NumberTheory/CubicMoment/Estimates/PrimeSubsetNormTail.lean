import OAI.NumberTheory.CubicMoment.Estimates.NormSeries
import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius

namespace OAI

/-! The sum over distinct prime subsets has no multiplicity loss after
mapping each subset to its primary product. A convergent lattice norm
series therefore controls its inverse-square tail. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primary_prime_subset_norm_sum (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (A : Finset (Finset Eisenstein))
    (hA : A ⊆ U.powerset) {s : ℝ} (hs : 1 < s) :
    (∑ d ∈ A, norm (∏ p ∈ d,p)^(-s)) ≤
      ∑' n : Eisenstein, norm n^(-s) := by
  have hinj : Set.InjOn (fun d : Finset Eisenstein => ∏ p ∈ d,p) (↑A : Set _) := by
    intro d hd e he hde
    exact primaryPrimeFactors_prod_injective hU (hA hd) (hA he) hde
  calc
    _ = ∑ n ∈ A.image (fun d : Finset Eisenstein => ∏ p ∈ d,p), norm n^(-s) :=
      (Finset.sum_image (f := fun n : Eisenstein => norm n^(-s)) hinj).symm
    _ ≤ _ := (summable_eisenstein_norm_rpow hs).sum_le_tsum _
      (fun n _ => Real.rpow_nonneg (norm_nonneg n) _)

theorem primary_prime_subset_harmonic (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    (∑ d ∈ U.powerset.filter (fun d => norm (∏ p ∈ d,p) ≤ b),
      (norm (∏ p ∈ d,p))⁻¹) ≤
      b^ε*(∑' n : Eisenstein, norm n^(-(1+ε))) := by
  let A := U.powerset.filter (fun d => norm (∏ p ∈ d,p) ≤ b)
  have hp (d : Finset Eisenstein) (hd : d ∈ A) :
      (norm (∏ p ∈ d,p))⁻¹ ≤ b^ε*norm (∏ p ∈ d,p)^(-(1+ε)) := by
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1
    have hdp := norm_pos_of_ne_zero (primary_ne_zero
      (primary_finset_prod d (fun p => p) (fun p hp => (hU p (hsub hp)).1)))
    have he : (norm (∏ p ∈ d,p))⁻¹ =
        norm (∏ p ∈ d,p)^ε*norm (∏ p ∈ d,p)^(-(1+ε)) := by
      rw [←Real.rpow_add hdp]
      rw [show ε+ -(1+ε) = (-1:ℝ) by ring,Real.rpow_neg_one]
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hdp.le (Finset.mem_filter.mp hd).2 hε.le) (by positivity)
  calc
    _ ≤ ∑ d ∈ A, b^ε*norm (∏ p ∈ d,p)^(-(1+ε)) := Finset.sum_le_sum hp
    _ = b^ε*(∑ d ∈ A, norm (∏ p ∈ d,p)^(-(1+ε))) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (primary_prime_subset_norm_sum U hU A (fun _ hd => (Finset.mem_filter.mp hd).1)
        (by linarith : 1 < 1+ε)) (Real.rpow_nonneg hb.le _)

lemma finite_eisenstein_norm_square_tail (S : Finset Eisenstein) {D : ℝ}
    (hD : 0 < D) (hS : ∀ n ∈ S, D < norm n) :
    (∑ n ∈ S, norm n^(-2:ℝ)) ≤
      D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) := by
  calc
    _ ≤ ∑ n ∈ S, D^(-(1/2:ℝ))*norm n^(-(3/2:ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [show (3/2:ℝ)-2 = -(1/2:ℝ) by norm_num] using
        norm_rpow_tail_pointwise (s := 3/2) (t := 2) hD (by norm_num) (hS n hn)
    _ = D^(-(1/2:ℝ))*(∑ n ∈ S, norm n^(-(3/2:ℝ))) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_eisenstein_norm_rpow (show (1:ℝ) < 3/2 by norm_num)).sum_le_tsum S
        (fun n _ => Real.rpow_nonneg (norm_nonneg n) _)) (by positivity)

theorem primary_prime_subset_norm_tail (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) {D : ℝ} (hD : 0 < D) :
    (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s,p)),
      norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) := by
  let S := U.powerset.filter (fun s => D < norm (∏ p ∈ s,p))
  have hinj : Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s,p) (↑S : Set _) := by
    intro s hs t ht he
    exact primaryPrimeFactors_prod_injective hU
      (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp ht).1 he
  calc
    _ = ∑ n ∈ S.image (fun s : Finset Eisenstein => ∏ p ∈ s,p), norm n^(-2:ℝ) :=
      (Finset.sum_image (f := fun n : Eisenstein => norm n^(-2:ℝ)) hinj).symm
    _ ≤ _ := finite_eisenstein_norm_square_tail _ hD (by
      intro n hn
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hn
      exact (Finset.mem_filter.mp hs).2)

end CubicFirstMoment

end

end OAI
