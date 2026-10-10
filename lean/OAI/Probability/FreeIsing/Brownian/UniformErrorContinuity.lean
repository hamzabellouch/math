import OAI.Probability.FreeIsing.Brownian.UniformGrid
import OAI.Probability.FreeIsing.Martingales.StrongMaximal

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.BrownianUniformErrorContinuity

open BrownianGrid MartingaleStrongMaximal

theorem uniformSum_sq_le {Ω : Type*} (B H : ℝ≥0 → Ω → ℝ)
    {ω : Ω} {T N : ℝ≥0} (hTN : T ≤ N) {C R : ℝ}
    (hC : 0 ≤ C) (hB : ∀ t ≤ N, B t ω ^ 2 ≤ R)
    (hH : ∀ t, |H t ω| ≤ C) (n : ℕ) :
    uniformSum B H T n ω ^ 2 ≤ 4 * (n : ℝ) ^ 2 * C ^ 2 * R := by
  let f : ℕ → ℝ := fun i => H (uniformGrid T n i) ω *
    (B (uniformGrid T n (i + 1)) ω - B (uniformGrid T n i) ω)
  have hterm (i : ℕ) (hi : i ∈ Finset.range n) : f i ^ 2 ≤ 4 * C ^ 2 * R := by
    have hin : i < n := Finset.mem_range.mp hi
    have hn : 0 < n := (Nat.zero_le i).trans_lt hin
    have ha := hB (uniformGrid T n i)
      ((uniformGrid_le_horizon T hn hin.le).trans hTN)
    have hb := hB (uniformGrid T n (i + 1))
      ((uniformGrid_le_horizon T hn (Nat.succ_le_of_lt hin)).trans hTN)
    have hcoef : H (uniformGrid T n i) ω ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hC).mpr (hH (uniformGrid T n i))
    have hinc : (B (uniformGrid T n (i + 1)) ω - B (uniformGrid T n i) ω) ^ 2 ≤ 4 * R := by
      nlinarith [sq_nonneg (B (uniformGrid T n (i + 1)) ω + B (uniformGrid T n i) ω)]
    calc
      f i ^ 2 = H (uniformGrid T n i) ω ^ 2 *
          (B (uniformGrid T n (i + 1)) ω - B (uniformGrid T n i) ω) ^ 2 := mul_pow _ _ _
      _ ≤ C ^ 2 * (4 * R) := mul_le_mul hcoef hinc (sq_nonneg _) (sq_nonneg _)
      _ = 4 * C ^ 2 * R := by ring
  calc
    uniformSum B H T n ω ^ 2 = (∑ i ∈ Finset.range n, f i) ^ 2 := rfl
    _ ≤ (n : ℝ) * ∑ i ∈ Finset.range n, f i ^ 2 := by
      simpa only [Finset.card_range] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := f))
    _ ≤ (n : ℝ) * ∑ _i ∈ Finset.range n, 4 * C ^ 2 * R :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg n)
    _ = 4 * (n : ℝ) ^ 2 * C ^ 2 * R := by simp; ring

theorem continuous_uniformSum_horizon {Ω : Type*} (B H : ℝ≥0 → Ω → ℝ)
    {ω : Ω} (hB : Continuous (fun t => B t ω))
    (hH : Continuous (fun t => H t ω)) (n : ℕ) :
    Continuous (fun T : ℝ≥0 => uniformSum B H T n ω) := by
  have hg (i : ℕ) : Continuous (fun T : ℝ≥0 => uniformGrid T n i) :=
    (continuous_id.const_mul (i : ℝ≥0)).div_const (n : ℝ≥0)
  unfold uniformSum integralSum
  apply continuous_finsetSum
  intro i _
  exact (hH.comp (hg i)).mul ((hB.comp (hg (i + 1))).sub (hB.comp (hg i)))

theorem continuousOn_uniformSum_meanSquare_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B H I : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B F P) (hI : Martingale I F P)
    (hB2 : ∀ t, MemLp (B t) 2 P) (hI2 : ∀ t, MemLp (I t) 2 P)
    (hcB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hcI : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hH : StronglyAdapted F H)
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (n : ℕ) (N : ℝ≥0) :
    ContinuousOn (fun T : ℝ≥0 => ∫ ω,
      (uniformSum B H T n ω - I T ω) ^ 2 ∂P) (Icc 0 N) := by
  have hmS (T : ℝ≥0) : AEStronglyMeasurable (uniformSum B H T n) P := by
    unfold uniformSum integralSum
    have hs := Finset.aestronglyMeasurable_sum (Finset.range n) (fun i _ =>
      (((hH (uniformGrid T n i)).mono (F.le _)).aestronglyMeasurable).mul
        ((hB2 (uniformGrid T n (i + 1))).aestronglyMeasurable.sub
          (hB2 (uniformGrid T n i)).aestronglyMeasurable))
    convert hs using 1
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
  let D : Ω → ℝ := fun ω =>
    (8 * (n : ℝ) ^ 2 * C ^ 2) * maximalSquare B N ω + 2 * maximalSquare I N ω
  apply continuousOn_of_dominated (bound := D)
  · intro T _
    exact ((hmS T).sub (hI2 T).aestronglyMeasurable).pow 2
  · intro T hT
    filter_upwards [hbH, ae_all_sq_le_maximalSquare hB hB2 hcB N,
      ae_all_sq_le_maximalSquare hI hI2 hcI N] with ω hHω hBω hIω
    have hS := uniformSum_sq_le B H hT.2 hC hBω hHω n
    have hIt := hIω T hT.2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    dsimp [D]
    nlinarith [sq_nonneg (uniformSum B H T n ω + I T ω)]
  · exact ((integrable_maximalSquare hB hB2 hcB N).const_mul _).add
      ((integrable_maximalSquare hI hI2 hcI N).const_mul 2)
  · filter_upwards [hcB, hcH, hcI] with ω hBω hHω hIω
    exact (((continuous_uniformSum_horizon B H hBω hHω n).sub hIω).pow 2).continuousOn

end Problem367.BrownianUniformErrorContinuity

end

end OAI
