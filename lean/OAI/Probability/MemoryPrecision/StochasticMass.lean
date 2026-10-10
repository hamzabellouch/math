import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeContinuation
import OAI.Probability.MemoryPrecision.StochasticContinuation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression
lemma stoch_sphere_mass {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N → ℝ≥0∞}
    {w : ℕ → Fin N → Sphere d → ℝ≥0∞}
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a))
    (hδ1 : ∀ n j obs, ∑ a, δ n j obs a ≤ 1) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1) {H α : ℝ} (hH : 0 < H)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2)
    (hlocal : ∀ n j, SphereBallBound (w n j) H α)
    (b k : ℕ) (hk : k ≤ b*(d/8)) (n : ℕ) (j : Fin N) :
    SphereBallBound (stochCont δ w Subtype.val n k j)
      (H * RealStep d N ^ b) α := by
  have hp : 0 < d/8 := by omega
  have hK := realStep_one d hN
  have hK0 := realStep_pos d hN
  induction b generalizing k n j with
  | zero =>
    have : k = 0 := by omega
    subst k
    simpa [stochCont] using hlocal n j
  | succ b ih =>
    by_cases hk0 : k = 0
    · subst k
      apply (hlocal n j).mono
      simpa [stochCont] using le_mul_of_one_le_right hH.le (one_le_pow₀ hK)
    · let m := min k (d/8)
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hmp : m ≤ d/8 := min_le_right _ _
      have hmk : m ≤ k := min_le_left _ _
      have hk' : k-m ≤ b*(d/8) := by
        dsimp [m]
        rw [Nat.succ_mul] at hk
        omega
      have hb := (Classical.choose_spec coefficient_step).2 d m N hd hm hmp hN α
        (H * RealStep d N ^ b) hαlo hαhi (mul_pos hH (pow_pos hK0 b))
        (fun a => stochCont δ w Subtype.val (n+m) (k-m) a)
        (fun a => measurable_stochCont hδ hw measurable_subtype_coe _ _ a)
        (fun a s => stochCont_le_one Subtype.val hδ1 hw1 _ _ a s)
        (fun a => ih (k-m) hk' (n+m) a)
        (fun a x => stochRoute δ n m j x a)
        (fun a => measurable_stochRoute hδ n m j a)
        (fun x => stochRoute_sum_le_one hδ1 n m j x)
      have he : stochCont δ w Subtype.val n k j =
          SphereBlock (fun a => stochCont δ w Subtype.val (n+m) (k-m) a)
            (fun a x => stochRoute δ n m j x a) := by
        funext s
        simpa [Nat.add_sub_of_le hmk, SphereBlock, WeightedBlock] using
          stochCont_unroll Subtype.val hδ n m (k-m) j s
      rw [he]
      convert hb using 1
      change H * RealStep d N ^ (b+1) = RealStep d N * (H * RealStep d N ^ b)
      rw [pow_succ]; ring

lemma stoch_cube_mass {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N → ℝ≥0∞}
    {w : ℕ → Fin N → Cube d → ℝ≥0∞}
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a))
    (hδ1 : ∀ n j obs, ∑ a, δ n j obs a ≤ 1) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1) {H : ℝ} (hH : 0 < H)
    (hlocal : ∀ n j, CubeLocal (w n j) H)
    (b k : ℕ) (hk : k ≤ b*((d/2)/4)) (n : ℕ) (j : Fin N) :
    CubeLocal (stochCont δ w (CubeEmbedding d) n k j)
      (H * CubeStep d N ^ b) := by
  have hp : 0 < (d/2)/4 := by omega
  have hK := cubeStep_one d hN
  have hK0 := cubeStep_pos d hN
  induction b generalizing k n j with
  | zero =>
    have : k = 0 := by omega
    subst k
    simpa [stochCont] using hlocal n j
  | succ b ih =>
    by_cases hk0 : k = 0
    · subst k
      apply (hlocal n j).mono
      simpa [stochCont] using le_mul_of_one_le_right hH.le (one_le_pow₀ hK)
    · let m := min k ((d/2)/4)
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hmp : m ≤ (d/2)/4 := min_le_right _ _
      have hmk : m ≤ k := min_le_left _ _
      have hk' : k-m ≤ b*((d/2)/4) := by
        dsimp [m]
        rw [Nat.succ_mul] at hk
        omega
      have hb := (Classical.choose_spec cube_block).2 d m N hd hm hmp hN
        (H * CubeStep d N ^ b) (mul_pos hH (pow_pos hK0 b)).le
        (fun a => stochCont δ w (CubeEmbedding d) (n+m) (k-m) a)
        (fun a => measurable_stochCont hδ hw (cubeEmbedding_measurable d) _ _ a)
        (fun a s => stochCont_le_one (CubeEmbedding d) hδ1 hw1 _ _ a s)
        (fun a => ih (k-m) hk' (n+m) a)
        (fun a x => stochRoute δ n m j x a)
        (fun a => measurable_stochRoute hδ n m j a)
        (fun x => stochRoute_sum_le_one hδ1 n m j x)
      have he : stochCont δ w (CubeEmbedding d) n k j =
          WeightedBlock (CubeEmbedding d)
            (fun a => stochCont δ w (CubeEmbedding d) (n+m) (k-m) a)
            (fun a x => stochRoute δ n m j x a) := by
        funext s
        simpa [Nat.add_sub_of_le hmk, WeightedBlock] using
          stochCont_unroll (CubeEmbedding d) hδ n m (k-m) j s
      rw [he]
      convert hb using 1
      change H * CubeStep d N ^ (b+1) = CubeStep d N * (H * CubeStep d N ^ b)
      rw [pow_succ]; ring

end MemoryPrecision


end

end OAI
