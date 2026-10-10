import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.CubeBlock
import OAI.Probability.MemoryPrecision.CubeCaps
import OAI.Probability.MemoryPrecision.RealContinuation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression
def CubeStepConstant : ℝ := Classical.choose cube_block
lemma cubeStepConstant_one : 1 ≤ CubeStepConstant := (Classical.choose_spec cube_block).1
lemma cubeStepConstant_pos : 0 < CubeStepConstant := lt_of_lt_of_le zero_lt_one cubeStepConstant_one

def CubeStep (d N : ℕ) : ℝ := CubeStepConstant^(d/2) * (N:ℝ)^(1/(((d/2)/4:ℕ):ℝ))
lemma cubeStep_one (d : ℕ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ CubeStep d N := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ cubeStepConstant_one
  · exact Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
lemma cubeStep_pos (d : ℕ) {N : ℕ} (hN : 1 ≤ N) : 0 < CubeStep d N :=
  lt_of_lt_of_le zero_lt_one (cubeStep_one d hN)

lemma cube_deterministic_step {d m N : ℕ} (hd : 16 ≤ d) (hm : 1 ≤ m)
    (hmp : m ≤ (d/2)/4) (hN : 1 ≤ N) {H : ℝ} (hH : 0 < H)
    (h : Fin N → Space d → ℝ≥0∞) (hh : ∀ w, Measurable (h w))
    (hh1 : ∀ w s, h w s ≤ 1)
    (hb : ∀ w, CubeLocal (fun u => h w (CubeEmbedding d u)) H)
    (φ : ((Fin m → Space d) × (Fin m → ℝ)) → Fin N) (hφ : Measurable φ) :
    CubeLocal (fun u => blockValue h φ (CubeEmbedding d u)) (CubeStep d N * H) := by
  classical
  let g (w : Fin N) (x : (Fin m → Space d) × (Fin m → ℝ)) : ℝ≥0∞ :=
    if φ x = w then 1 else 0
  have hg (w) : Measurable (g w) := by
    exact Measurable.ite (measurableSet_eq_fun hφ measurable_const) measurable_const measurable_const
  have hg1 (x) : ∑ w, g w x ≤ 1 := by simp [g]
  have hb' := (Classical.choose_spec cube_block).2 d m N hd hm hmp hN H hH.le
    (fun w u => h w (CubeEmbedding d u)) (fun w => (hh w).comp (cubeEmbedding_measurable d))
    (fun w u => hh1 w (CubeEmbedding d u)) hb g hg hg1
  convert hb' using 1
  · funext u
    unfold blockValue WeightedBlock
    congr 1
    funext A
    simp [g]
  · rfl

lemma CubeLocal.mono {d : ℕ} {h : Cube d → ℝ≥0∞} {H K : ℝ}
    (hh : CubeLocal h H) (hHK : H ≤ K) : CubeLocal h K := by
  intro z r hr
  exact (hh z r hr).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hHK (by positivity)))

lemma cube_continuation_mass {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N}
    {w : ℕ → Fin N → Space d → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1) {H : ℝ} (hH : 0 < H)
    (hlocal : ∀ n j, CubeLocal (fun s => w n j (CubeEmbedding d s)) H)
    (b k : ℕ) (hk : k ≤ b*((d/2)/4)) (n : ℕ) (j : Fin N) :
    CubeLocal (fun s => continuation δ w n k j (CubeEmbedding d s))
      (H * CubeStep d N ^ b) := by
  have hp : 0 < (d/2)/4 := by omega
  have hK := cubeStep_one d hN
  have hK0 := cubeStep_pos d hN
  induction b generalizing k n j with
  | zero =>
    have : k = 0 := by omega
    subst k
    simpa [continuation] using hlocal n j
  | succ b ih =>
    by_cases hk0 : k = 0
    · subst k
      apply (hlocal n j).mono
      simpa [continuation] using le_mul_of_one_le_right hH.le (one_le_pow₀ hK)
    · let m := min k ((d/2)/4)
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hmp : m ≤ (d/2)/4 := min_le_right _ _
      have hmk : m ≤ k := min_le_left _ _
      have hk' : k-m ≤ b*((d/2)/4) := by
        dsimp [m]
        rw [Nat.succ_mul] at hk
        omega
      have hb := cube_deterministic_step hd hm hmp hN
        (mul_pos hH (pow_pos hK0 b))
        (fun a => continuation δ w (n+m) (k-m) a)
        (fun a => measurable_continuation hδ hw _ _ a)
        (fun a s => continuation_le_one hw1 _ _ a s)
        (fun a => ih (k-m) hk' (n+m) a) (streamRoute δ n m j)
        (measurable_streamRoute hδ n m j)
      have he : (fun s : Cube d => continuation δ w n k j (CubeEmbedding d s)) =
          (fun s : Cube d => blockValue (fun a => continuation δ w (n+m) (k-m) a)
            (streamRoute δ n m j) (CubeEmbedding d s)) := by
        funext s
        simpa [Nat.add_sub_of_le hmk] using continuation_unroll hδ n m (k-m) j (CubeEmbedding d s)
      rw [he]
      convert hb using 1
      rw [pow_succ]; ring

lemma cube_continuation_cap_integral {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N} (hδ : ∀ n j, Measurable (δ n j))
    (y : ℕ → Fin N → Space d) {ε : ℝ} (hε : 0 < ε) (n k : ℕ) (j : Fin N) :
    (∫⁻ u, continuation δ (fun n j => capWeight (y n j) ε) n k j (CubeEmbedding d u) ∂CubeLaw d) ≤
      ENNReal.ofReal ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) * CubeStep d N ^ BlockCount k ((d/2)/4)) := by
  apply cube_mass_bound
  apply cube_continuation_mass hd hN hδ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _) (by positivity)
    (fun n j => cube_cap_local (by omega) (y n j) hε)
  simpa [mul_comm] using blockCount_mul_ge k (by omega : 0 < (d/2)/4)

end MemoryPrecision


end

end OAI
