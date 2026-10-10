import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace Problem367.CompensatorVariation

def squaredIncrements (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, (a (i + 1) - a i) ^ 2

theorem squaredIncrements_nonneg (a : ℕ → ℝ) (N : ℕ) :
    0 ≤ squaredIncrements a N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem squaredIncrements_le {a : ℕ → ℝ} {N : ℕ} {δ : ℝ}
    (hpos : ∀ i < N, 0 ≤ a (i + 1) - a i)
    (hsmall : ∀ i < N, a (i + 1) - a i ≤ δ) :
    squaredIncrements a N ≤ δ * (a N - a 0) := by
  calc
    squaredIncrements a N ≤ ∑ i ∈ Finset.range N, δ * (a (i + 1) - a i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hsmall i (Finset.mem_range.mp hi))
        (hpos i (Finset.mem_range.mp hi))
    _ = δ * (a N - a 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]

theorem squaredIncrements_le_total_sq {a : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ i < N, 0 ≤ a (i + 1) - a i) :
    squaredIncrements a N ≤ (a N - a 0) ^ 2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.range N) (fun i hi => hpos i (Finset.mem_range.mp hi))
  simpa only [squaredIncrements, Finset.sum_range_sub] using h

theorem total_nonneg {a : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ i < N, 0 ≤ a (i + 1) - a i) : 0 ≤ a N - a 0 := by
  rw [← Finset.sum_range_sub a N]
  exact Finset.sum_nonneg (fun i hi => hpos i (Finset.mem_range.mp hi))

theorem increment_le_total {a : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ i < N, 0 ≤ a (i + 1) - a i) {i : ℕ} (hi : i < N) :
    a (i + 1) - a i ≤ a N - a 0 := by
  rw [← Finset.sum_range_sub a N]
  exact Finset.single_le_sum (fun j hj => hpos j (Finset.mem_range.mp hj))
    (Finset.mem_range.mpr hi)

theorem tendsto_squaredIncrements {I : Type*} [PseudoMetricSpace I]
    {K : Set I} (hK : IsCompact K) {A : I → ℝ} (hA : ContinuousOn A K)
    (t : ℕ → ℕ → I) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ K)
    (hdist : ∀ n i, i < N n → dist (t n i) (t n (i + 1)) ≤ mesh n)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n i, i < N n → 0 ≤ A (t n (i + 1)) - A (t n i))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, A (t n (N n)) - A (t n 0) ≤ C) :
    Tendsto (fun n => squaredIncrements (fun i => A (t n i)) (N n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (C + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hA) η hη
  obtain ⟨n₀, hn₀⟩ := (hmesh.eventually (gt_mem_nhds hδ)).exists_forall_of_atTop
  refine ⟨n₀, ?_⟩
  intro n hn
  have hsmall (i : ℕ) (hi : i < N n) : A (t n (i + 1)) - A (t n i) ≤ η := by
    have hh := hmod (t n (i + 1)) (hmem n (i + 1) (Nat.succ_le_of_lt hi))
      (t n i) (hmem n i hi.le) (by
        rw [dist_comm]
        exact (hdist n i hi).trans_lt (hn₀ n hn))
    exact (le_abs_self _).trans (by simpa only [Real.dist_eq] using hh.le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (squaredIncrements_nonneg _ _)]
  calc
    squaredIncrements (fun i => A (t n i)) (N n) ≤
        η * (A (t n (N n)) - A (t n 0)) := squaredIncrements_le (hpos n) hsmall
    _ ≤ η * C := mul_le_mul_of_nonneg_left (hbound n) hη.le
    _ < ε := by
      change ε / (C + 1) * C < ε
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by linarith : 0 < C + 1)).2
      nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem memLp_increment_of_total_bound [IsFiniteMeasure μ]
    {a : ℕ → Ω → ℝ} (hmeas : ∀ i, AEStronglyMeasurable (a i) μ) {N : ℕ}
    (hpos : ∀ᵐ ω ∂μ, ∀ i < N, 0 ≤ a (i + 1) ω - a i ω)
    {C : ℝ} (hbound : ∀ᵐ ω ∂μ, a N ω - a 0 ω ≤ C)
    {i : ℕ} (hi : i < N) (p : ℝ≥0∞) :
    MemLp (fun ω => a (i + 1) ω - a i ω) p μ := by
  apply MemLp.of_bound ((hmeas _).sub (hmeas _)) C
  filter_upwards [hpos, hbound] with ω hp hb
  rw [Real.norm_eq_abs, Pi.sub_apply, abs_of_nonneg (hp i hi)]
  exact (increment_le_total (a := fun j => a j ω) hp hi).trans hb

theorem tendsto_integral_squaredIncrements [IsFiniteMeasure μ]
    {I : Type*} [PseudoMetricSpace I] {K : Set I} (hK : IsCompact K)
    {A : I → Ω → ℝ} (hmeas : ∀ t, AEStronglyMeasurable (A t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) K)
    (t : ℕ → ℕ → I) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ K)
    (hdist : ∀ n i, i < N n → dist (t n i) (t n (i + 1)) ≤ mesh n)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ᵐ ω ∂μ, ∀ n i, i < N n → 0 ≤ A (t n (i + 1)) ω - A (t n i) ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂μ, ∀ n, A (t n (N n)) ω - A (t n 0) ω ≤ C) :
    Tendsto (fun n => ∫ ω, squaredIncrements (fun i => A (t n i) ω) (N n) ∂μ)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun ω => squaredIncrements (fun i => A (t n i) ω) (N n)) μ := by
    convert (Finset.aestronglyMeasurable_sum (Finset.range (N n))
      (fun i _ => ((hmeas (t n (i + 1))).sub (hmeas (t n i))).pow 2)) using 1
    ext ω
    simp only [squaredIncrements, Finset.sum_apply, Pi.pow_apply, Pi.sub_apply]
  have hh := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n ω => squaredIncrements (fun i => A (t n i) ω) (N n))
    (f := fun _ => (0 : ℝ)) (fun _ => C ^ 2) hm (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using hh
  · intro n
    filter_upwards [hpos, hbound] with ω hp hb
    rw [Real.norm_eq_abs, abs_of_nonneg (squaredIncrements_nonneg _ _)]
    exact (squaredIncrements_le_total_sq (hp n)).trans
      ((sq_le_sq₀ (total_nonneg (a := fun i => A (t n i) ω) (hp n)) hC).2 (hb n))
  · filter_upwards [hc, hpos, hbound] with ω hω hp hb
    exact tendsto_squaredIncrements hK hω t N mesh hmem hdist hmesh hp hC hb

theorem tendsto_sum_integral_sq_increments [IsFiniteMeasure μ]
    {I : Type*} [PseudoMetricSpace I] {K : Set I} (hK : IsCompact K)
    {A : I → Ω → ℝ} (hmeas : ∀ t, AEStronglyMeasurable (A t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) K)
    (t : ℕ → ℕ → I) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ K)
    (hdist : ∀ n i, i < N n → dist (t n i) (t n (i + 1)) ≤ mesh n)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ᵐ ω ∂μ, ∀ n i, i < N n → 0 ≤ A (t n (i + 1)) ω - A (t n i) ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂μ, ∀ n, A (t n (N n)) ω - A (t n 0) ω ≤ C) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have heq (n : ℕ) : (∑ i ∈ Finset.range (N n),
      ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ) =
      ∫ ω, squaredIncrements (fun i => A (t n i) ω) (N n) ∂μ := by
    symm
    apply integral_finsetSum
    intro i hi
    apply (memLp_increment_of_total_bound (fun j => hmeas (t n j))
      (hpos.mono (fun ω hω => hω n))
      (hbound.mono (fun ω hω => hω n)) (Finset.mem_range.mp hi) 2).integrable_sq
  simp_rw [heq]
  exact tendsto_integral_squaredIncrements hK hmeas hc t N mesh hmem hdist hmesh hpos hC hbound

end Problem367.CompensatorVariation

end

end OAI
