import OAI.NumberTheory.CubicMoment.Estimates.SparseBilinearPowers

namespace OAI

/-! A polynomial logarithmic number of sparse stopping pieces retains
one common positive power saving. The finite coefficients may vary. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma sparse_logarithmic_piece_sum {τ K M : ℝ}
    (hτ : 0 < τ) (hK : 0 ≤ K) (hM : 0 ≤ M) (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (S : Finset ι) (c F : ι → ℂ) (X : ℝ),
      1 ≤ X → (S.card:ℝ) ≤ M*(1+Real.log X)^d →
      (∀ i ∈ S, ‖c i‖ ≤ 1) → (∀ i ∈ S, ‖F i‖ ≤ K*X^(5/6-τ)) →
      ‖∑ i ∈ S, c i*F i‖ ≤ C*X^(5/6-τ/2) := by
  obtain ⟨H,hH,hlog⟩ := log_power_normalization_bound d (show 0 < τ/2 by positivity)
  refine ⟨K*M*(H+1)+1,by positivity,?_⟩
  intro ι S c F X hX hcard hc hF
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : (1+Real.log X)^d ≤ (H+1)*X^(τ/2) := by
    have hh := mul_le_mul_of_nonneg_right ((hlog X hX).trans (show H ≤ H+1 by linarith))
      (Real.rpow_nonneg hXp.le (τ/2))
    have he : X^(-(τ/2))*X^(τ/2) = 1 := by rw [←Real.rpow_add hXp]; simp
    calc
      _ = (X^(-(τ/2))*X^(τ/2))*(1+Real.log X)^d := by rw [he,one_mul]
      _ = X^(-(τ/2))*(1+Real.log X)^d*X^(τ/2) := by ring
      _ ≤ _ := hh
  calc
    _ ≤ ∑ _i ∈ S, K*X^(5/6-τ) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hc i hi) (_root_.norm_nonneg _)).trans
        (by simpa only [one_mul] using hF i hi)
    _ = (S.card:ℝ)*(K*X^(5/6-τ)) := by simp
    _ ≤ (M*(1+Real.log X)^d)*(K*X^(5/6-τ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (M*((H+1)*X^(τ/2)))*(K*X^(5/6-τ)) := by gcongr
    _ = (K*M*(H+1))*X^(5/6-τ/2) := by
      rw [show M*((H+1)*X^(τ/2))*(K*X^(5/6-τ)) =
        (K*M*(H+1))*(X^(τ/2)*X^(5/6-τ)) by ring,←Real.rpow_add hXp]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hXp.le _)

end CubicFirstMoment

end

end OAI
