import OAI.NumberTheory.JointDickman.Counting.BlockOriginSum
import OAI.NumberTheory.JointDickman.Amplification.GraphBoundaryCap

namespace OAI

/-! # The original block average reduces to a finite counting prefix -/
namespace JointDickman
open Finset Classical

theorem arithmeticBlockAverage_prefix_bound {B L T H M N : ℕ} {τ C R : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hM : 0 < M) (hR : 0 ≤ R)
    (hraw : ∀ j n, rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) ≤ R)
    (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 2) :
    |arithmeticBlockAverage B L τ C T N H M F| ≤
      16*(M : ℝ)^2*R/((T : ℝ)*N)+
      (∑ u ∈ range (2*T*N),
        |(complexEnergy (finiteGraphKernel B L T H M N u τ C)
          (fun i => F (u+(i.val+1)))).re|/(M : ℝ))/((T : ℝ)*N) := by
  let f := fun s : ℤ =>
    |(complexEnergy (arithmeticBlockMatrix B L τ C T N H M s) (blockLabels M s F)).re|/(M : ℝ)
  have hf : ∀ s, 0 ≤ f s := fun s => div_nonneg (abs_nonneg _) (Nat.cast_nonneg M)
  have hs : ∀ s : ℤ, (2*T*N : ℕ) ≤ s → f s = 0 := by
    intro s hs
    have hs0 : 0 ≤ s := (by positivity : (0 : ℤ) ≤ (2*T*N : ℕ)).trans hs
    have he : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs0
    have hn : 2*T*N ≤ s.toNat := by omega
    dsimp only [f]
    rw [← he,arithmeticBlockMatrix_energy_scale,
      finiteGraphKernel_counting_support hB hT hn]
    simp [complexEnergy]
  have hsum := blockOrigins_sum_bound M (arithmeticGraphVertexCap B N) (2*T*N) f
    (show 0 ≤ 16*(M : ℝ)*(R/((T : ℝ)*N)) by positivity) hf
    (fun s _ => arithmeticBlockMatrix_energy_cap hM hR hraw s F hF) hs
  have hstart : |arithmeticBlockAverage B L τ C T N H M F| ≤
      ∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N), f s := by
    rw [arithmeticBlockAverage_matrix]
    simp only [abs_div,abs_of_nonneg (show (0 : ℝ) ≤ M from Nat.cast_nonneg M)]
    exact (div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg M)).trans_eq (sum_div _ _ _)
  apply hstart.trans (hsum.trans_eq ?_)
  have hpoint (u : ℕ) : f (u : ℤ) =
      (|(complexEnergy (finiteGraphKernel B L T H M N u τ C)
          (fun i => F (u+(i.val+1)))).re|/(M : ℝ))/((T : ℝ)*N) := by
    dsimp only [f]
    rw [arithmeticBlockMatrix_energy_scale,abs_div,abs_of_nonneg (by positivity : 0 ≤ (T : ℝ)*N)]
    ring
  simp_rw [hpoint]
  rw [← sum_div]
  ring

end JointDickman

end OAI
