import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylDifference
import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylWitnessVariation
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationSmoothing

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem exists_large_partial_sum_of_cutoff_weighted (a : ℕ → ℂ) {N d x H : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hdN : d ≤ N) (hx : 0 ≤ x) (hxd : x ≤ d)
    (J : ℕ) (hJ : (J : ℝ) ≤ N / d + 1)
    (hlarge : H ≤ ‖∑ j ∈ Finset.range J, a j * progressionCutoffWeight N d x j‖) :
    ∃ n ≤ J, H / (10 * cutoffFourierBound) ≤ ‖∑ j ∈ Finset.range n, a j‖ := by
  classical
  have hr : (Finset.range (J + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image (Finset.range (J + 1))
    (fun n => ‖∑ j ∈ Finset.range n, a j‖) hr
  have hnJ : n ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hb : ∀ m ≤ J, ‖∑ j ∈ Finset.range m, a j‖ ≤ ‖∑ j ∈ Finset.range n, a j‖ := by
    intro m hm
    exact hmax m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  have habel := finite_abel_norm_bound a (progressionCutoffWeight N d x) J
    (norm_nonneg (∑ j ∈ Finset.range n, a j)) hb
  have hvar := progression_cutoff_variation_le hN hd hdN hx hxd J hJ
  have hcost := mul_le_mul_of_nonneg_left hvar (norm_nonneg (∑ j ∈ Finset.range n, a j))
  refine ⟨n, hnJ, (div_le_iff₀ (mul_pos (by norm_num) cutoffFourierBound_pos)).mpr ?_⟩
  exact hlarge.trans (habel.trans hcost)

theorem progression_weyl_sum_eq (α d x : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, weylPhase (α * (x + d * (j : ℝ)) ^ 2)) =
      weylPhase (α * x ^ 2) * quadraticWeylSum (α * d ^ 2) (2 * α * d * x) 0 n := by
  unfold quadraticWeylSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← weylPhase_add]
  congr 1
  ring

lemma progression_weyl_sum_norm (α d x : ℝ) (n : ℕ) :
    ‖∑ j ∈ Finset.range n, weylPhase (α * (x + d * (j : ℝ)) ^ 2)‖ =
      ‖quadraticWeylSum (α * d ^ 2) (2 * α * d * x) 0 n‖ := by
  rw [progression_weyl_sum_eq, norm_mul, weylPhase_norm, one_mul]

lemma quadraticWeylSum_norm_le_length (α β start : ℝ) (n : ℕ) :
    ‖quadraticWeylSum α β start n‖ ≤ n := by
  unfold quadraticWeylSum
  calc
    _ ≤ ∑ j ∈ Finset.range n, ‖weylPhase (α * (start + j) ^ 2 + β * (start + j))‖ :=
      norm_sum_le _ _
    _ = _ := by simp

theorem exists_quadraticWeylSum_of_weighted_progression {N d x α ε : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hdN : d ≤ N) (hx : 0 ≤ x) (hxd : x ≤ d)
    (J : ℕ) (hJ : (J : ℝ) ≤ N / d + 1)
    (hlarge : (N / d) * ε ≤
      ‖∑ j ∈ Finset.range J,
        weylPhase (α * (x + d * (j : ℝ)) ^ 2) * progressionCutoffWeight N d x j‖) :
    ∃ n ≤ J,
      ((N / d) * ε) / (10 * cutoffFourierBound) ≤
        ‖quadraticWeylSum (α * d ^ 2) (2 * α * d * x) 0 n‖ ∧
      ((N / d) * ε) / (10 * cutoffFourierBound) ≤ (n : ℝ) := by
  obtain ⟨n, hn, hsum⟩ := exists_large_partial_sum_of_cutoff_weighted
    (fun j => weylPhase (α * (x + d * (j : ℝ)) ^ 2)) hN hd hdN hx hxd J hJ hlarge
  rw [progression_weyl_sum_norm] at hsum
  exact ⟨n, hn, hsum, hsum.trans (quadraticWeylSum_norm_le_length _ _ _ _)⟩

end Ostmann.QuadraticCenter

end

end OAI
