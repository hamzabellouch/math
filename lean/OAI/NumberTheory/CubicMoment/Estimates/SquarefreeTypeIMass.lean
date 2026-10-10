import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductMoment
import OAI.NumberTheory.CubicMoment.Estimates.RoughMoebius

namespace OAI

/-! The coefficient mass for the actual squarefree Type-I outer levels.
Only the primary-prime theorem enters the divisor moment. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma squarefree_primary_divisor_card_le {n : Eisenstein}
    (hn : primary n) (hs : Squarefree n) :
    (metaplecticPrimaryDivisors n).card ≤ 2^(primaryPrimeFactors n).card := by
  rw [primary_divisors_of_squarefree_eq hn hs]
  exact (Finset.card_image_le).trans_eq (Finset.card_powerset _)

theorem squarefree_typeI_coefficient_mass (hpnt : PrimaryPrimePNT)
    {M : ℝ} (hM : 0 ≤ M) (k : ℕ) :
    ∃ (K : ℝ) (d : ℕ), 0 ≤ K ∧ ∀ (X R : ℝ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ), 1 ≤ R → R ≤ X → 1 ≤ Real.log X →
      (∀ r ∈ S, primary r ∧ Squarefree r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, ‖α r‖ ≤ M*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      (∑ r ∈ S, ‖α r‖) ≤ K*R*(Real.log X)^d := by
  obtain ⟨C,d,hC,hmoment⟩ := squarefree_fixed_divisor_moment hpnt ((2:ℝ)^k) (by positivity)
  let A : ℝ := 2+Real.exp 1
  have hA : 1 < A := by dsimp [A]; linarith [Real.exp_pos (1:ℝ)]
  have hAl : 0 ≤ Real.log A := Real.log_nonneg hA.le
  refine ⟨M*C*A*(2+Real.log A)^d,d,by positivity,?_⟩
  intro X R S α hR hRX hlog hS hα
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hXp : 0 < X := hRp.trans_le hRX
  have hAR : Real.exp 1 ≤ A*R := by
    calc
      Real.exp 1 ≤ A := by dsimp [A]; linarith
      _ ≤ A*R := le_mul_of_one_le_right (zero_le_one.trans hA.le) hR
  have htwo : 2*R ≤ A*R := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith [Real.exp_pos (1:ℝ)]) hRp.le
  have hm := hmoment (A*R) S hAR (fun r hr =>
    ⟨(hS r hr).1,(hS r hr).2.1,(hS r hr).2.2.trans htwo⟩)
  have hL : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hlogs : 1+Real.log (A*R) ≤ (2+Real.log A)*Real.log X := by
    rw [Real.log_mul (by positivity : A ≠ 0) hRp.ne']
    have hrl : Real.log R ≤ Real.log X := Real.log_le_log hRp hRX
    nlinarith [mul_nonneg hAl (sub_nonneg.mpr hlog)]
  calc
    _ ≤ ∑ r ∈ S, M*((2:ℝ)^k)^(primaryPrimeFactors r).card := by
      apply Finset.sum_le_sum
      intro r hr
      apply (hα r hr).trans
      have hc : ((metaplecticPrimaryDivisors r).card:ℝ) ≤ (2:ℝ)^(primaryPrimeFactors r).card := by
        exact_mod_cast squarefree_primary_divisor_card_le (hS r hr).1 (hS r hr).2.1
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc k) hM
      simpa only [←pow_mul,mul_comm k] using hh
    _ = M*∑ r ∈ S, ((2:ℝ)^k)^(primaryPrimeFactors r).card := by rw [Finset.mul_sum]
    _ ≤ M*(C*(A*R)*(1+Real.log (A*R))^d) := mul_le_mul_of_nonneg_left hm hM
    _ ≤ M*(C*(A*R)*((2+Real.log A)*Real.log X)^d) := by
      gcongr
      · linarith [Real.log_nonneg (show 1 ≤ A*R by nlinarith)]
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI
