import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimeScale

namespace OAI

/-! Summing the actual geometric-bin complexity consumes only its
explicit logarithmic power. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem geometric_bin_log_saving {X B δ C H D K b : ℝ}
    (hX : 0 < X) (hL : 1 ≤ Real.log X) (hB : 1 ≤ B) (hBX : B ≤ X^C)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hwidth : (Real.log X)^(-H) ≤ δ) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (S : Finset ℕ) (hS : S ⊆ Finset.range (geometricBinCount (1+δ) B))
    (f : ℕ → ℂ) (hf : ∀ j ∈ S, ‖f j‖ ≤ K*b/(Real.log X)^(D+H+1)) :
    ‖∑ j ∈ S, f j‖ ≤ ((2*C+1)*K)*b/(Real.log X)^D := by
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL
  have hcount : (S.card:ℝ) ≤ (2*C+1)*(Real.log X)^(H+1) := by
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card hS))
    simpa only [Finset.card_range] using
      geometricBinCount_logarithmic_width hX hL hB hBX hC hH hδ hδone hwidth
  calc
    _ ≤ ∑ _j ∈ S, K*b/(Real.log X)^(D+H+1) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hf)
    _ = (S.card:ℝ)*(K*b/(Real.log X)^(D+H+1)) := by simp
    _ ≤ ((2*C+1)*(Real.log X)^(H+1))*(K*b/(Real.log X)^(D+H+1)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by
      have he : (Real.log X)^(D+H+1) =
          (Real.log X)^D*(Real.log X)^(H+1) := by
        rw [show D+H+1 = D+(H+1) by ring,Real.rpow_add hLp]
      rw [he]
      field_simp

end CubicFirstMoment

end

end OAI
