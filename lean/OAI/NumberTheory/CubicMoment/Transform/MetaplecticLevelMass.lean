import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticAuxiliary
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorMoments

namespace OAI

/-! The actual primary divisor bound supplies both outer coefficient
masses needed by the counting and cubic-sieve parts of Type I. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_level_masses (S : Finset Eisenstein) (α : Eisenstein → ℂ)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hS : ∀ r ∈ S, primary r ∧ norm r ≤ 2*R)
    (hα : ∀ r ∈ S, ‖α r‖ ≤ M) :
    (∑ r ∈ S, ‖α r‖) ≤ 36*R*M ∧ (∑ r ∈ S, ‖α r‖^2) ≤ 36*R*M^2 := by
  have hsub : S ⊆ primaryElementBall (2*R) := fun r hr => mem_primaryElementBall.mpr (hS r hr)
  have hc : (S.card:ℝ) ≤ 36*R :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((primaryElementBall_card_le (by positivity)).trans_eq (by ring))
  constructor
  · calc
      _ ≤ ∑ _r ∈ S, M := Finset.sum_le_sum hα
      _ = (S.card:ℝ)*M := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hM
  · calc
      _ ≤ ∑ _r ∈ S, M^2 := Finset.sum_le_sum
        (fun r hr => pow_le_pow_left₀ (_root_.norm_nonneg _) (hα r hr) 2)
      _ = (S.card:ℝ)*M^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem metaplectic_divisor_coefficient_power {ε A : ℝ} (hε : 0 < ε)
    (hA : 0 ≤ A) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (r : Eisenstein), primary r →
      ∀ X : ℝ, 1 ≤ X → norm r ≤ 2*X → ∀ z : ℂ,
      ‖z‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k → ‖z‖ ≤ D*X^ε := by
  let δ : ℝ := ε/((k:ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have he : δ*(k:ℝ) ≤ ε := by
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hd : δ*((k:ℝ)+1) = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power hδ
  refine ⟨A*C^k*2^ε,by positivity,?_⟩
  intro r hr X hX hNr z hz
  have hnr : 1 ≤ norm r := one_le_norm (primary_ne_zero hr)
  have hc : ((metaplecticPrimaryDivisors r).card:ℝ) ≤ C*norm r^δ := by
    exact hdiv (primaryElementBall (norm r))
      (fun a ha => (mem_primaryElementBall.mp ha).1) r (primary_ne_zero hr)
  have hp : norm r^(δ*(k:ℝ)) ≤ (2*X)^ε :=
    (Real.rpow_le_rpow_of_exponent_le hnr he).trans
      (Real.rpow_le_rpow (norm_nonneg _) hNr hε.le)
  calc
    _ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k := hz
    _ ≤ A*(C*norm r^δ)^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hc k) hA
    _ = (A*C^k)*norm r^(δ*(k:ℝ)) := by
      rw [mul_pow,←Real.rpow_mul_natCast (norm_nonneg r)]
      ring
    _ ≤ (A*C^k)*(2*X)^ε := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ X)]; ring

end CubicFirstMoment

end

end OAI
