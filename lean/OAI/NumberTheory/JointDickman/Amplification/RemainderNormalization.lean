import OAI.NumberTheory.JointDickman.Amplification.WeightedRemainderLaw
import OAI.NumberTheory.JointDickman.Probability.GraphResidueNormalization

namespace OAI

/-! # Uniform normalization of the first-representation measure -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem remainderTiltNormalizer_nonneg (B : ℕ) (A : Finset ℕ) :
    0 ≤ remainderTiltNormalizer B A := by
  apply mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _)
  apply prod_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))

/-- Removing the finitely many forced coefficient primes changes the
normalization by a bounded factor, uniformly in the coefficient. -/
theorem remainderTiltNormalizer_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ A ⊆ auxiliaryPrimes B, (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        remainderTiltNormalizer B A ≤ K := by
  let C : ℝ := (4 : ℝ)^(-(1/2 : ℝ))+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C*Real.exp 1,by positivity,?_⟩
  have ht := auxiliary_primeNormalizer_tendsto hM (z := 1/2) (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (Iio_mem_nhds (show (4 : ℝ)^(-(1/2 : ℝ)) < C by
      dsimp [C]; linarith)),auxiliary_selected_odds_bound] with B hbase hodds
  intro A hA hsize
  unfold remainderTiltNormalizer
  rw [primeNormalizer_sdiff hA (auxiliaryPrimes_prime B),← mul_assoc]
  exact mul_le_mul (by simpa only [mul_comm] using hbase.le) (hodds A hA hsize)
    (prod_nonneg fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p (hA hp)).two_le
      apply inv_nonneg.mpr
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))) hC.le

end JointDickman

end OAI
