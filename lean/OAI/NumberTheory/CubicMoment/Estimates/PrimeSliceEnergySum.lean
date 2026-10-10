import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeSlice
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDivisorSubsets
import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius

namespace OAI

/-! Sum the shortened coefficient energies over common divisors without
paying for the ambient prime set. Each n-fold prime product has at most
2^n subsets of prime divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrime_divisor_energy_eq_slice {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) {f : Eisenstein} (hf : primary f)
    (e : Eisenstein) :
    (∑ b ∈ (fullSquarefreePrimeSupport R W X e).filter (fun b => f ∣ b),
      ‖fullPrimeCoefficient R W X b‖^2) =
    ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
  have hh := fullPrime_divisor_sum_eq_slice W X hX hlo hhi hf e
    (fun b => (‖fullPrimeCoefficient R W X b‖^2 : ℝ) : Eisenstein → ℂ)
  exact_mod_cast hh

lemma fullPrime_summed_slice_energy {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) (e : Eisenstein)
    (U : Finset Eisenstein) (hU : ∀ p ∈ U, primaryPrime p) :
    (∑ s ∈ U.powerset, ∑ n ∈ fullPrimeSliceSupport R W X (∏ p ∈ s, p) e,
      ‖fullPrimeCoefficient R W X ((∏ p ∈ s, p)*n)‖^2) ≤
    (2^Fintype.card ι:ℝ)*∑ b ∈ fullSquarefreePrimeSupport R W X e,
      ‖fullPrimeCoefficient R W X b‖^2 := by
  have heq (s : Finset Eisenstein) (hs : s ∈ U.powerset) :=
    fullPrime_divisor_energy_eq_slice W X hX hlo hhi
      (primary_finset_prod s (fun p : Eisenstein => p)
        (fun p hp => (hU p (Finset.mem_powerset.mp hs hp)).1)) e
  calc
    _ = ∑ s ∈ U.powerset, ∑ b ∈ (fullSquarefreePrimeSupport R W X e).filter
        (fun b => (∏ p ∈ s, p) ∣ b), ‖fullPrimeCoefficient R W X b‖^2 :=
      Finset.sum_congr rfl (fun s hs => (heq s hs).symm)
    _ = ∑ b ∈ fullSquarefreePrimeSupport R W X e,
        ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card:ℝ)*
          ‖fullPrimeCoefficient R W X b‖^2 := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ ∑ b ∈ fullSquarefreePrimeSupport R W X e,
        (2^Fintype.card ι:ℝ)*‖fullPrimeCoefficient R W X b‖^2 := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast fullPrime_divisor_subsets_card R W X e U hU hb
    _ = _ := (Finset.mul_sum _ _ _).symm

end CubicFirstMoment

end

end OAI
