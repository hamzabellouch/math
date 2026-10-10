import OAI.Probability.FreeIsing.Martingales.PredictableMeshApproximation
import OAI.Probability.FreeIsing.Martingales.SquareMaximal

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleSquareMaximal

private def dyadicPoint (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 ^ n : ℕ)

private lemma dyadicPoint_mono (n : ℕ) : Monotone (dyadicPoint n) := by
  intro i j hij
  dsimp [dyadicPoint]
  gcongr

private lemma dyadicPoint_double (n k : ℕ) :
    dyadicPoint (n + 1) (2 * k) = dyadicPoint n k := by
  simp only [dyadicPoint, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

private lemma dyadicPoint_eq_mesh (n k : ℕ) :
    dyadicPoint n k = PredictableMesh.point (2 ^ n - 1) k := by
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  simp only [dyadicPoint, PredictableMesh.point, Nat.sub_add_cancel hn]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

theorem continuous_maximal_sq
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (ε T : ℝ≥0) :
    (ε : ℝ≥0∞) ^ 2 * μ {ω | ∃ t ≤ T, (ε : ℝ) < |M t ω|} ≤
      ENNReal.ofReal (∫ ω, M T ω ^ 2 ∂μ) := by
  let A : ℕ → Set Ω := fun n =>
    {ω | ∃ k : ℕ, dyadicPoint n k ≤ T ∧ (ε : ℝ) < |M (dyadicPoint n k) ω|}
  have hAmono : Monotone A := by
    apply monotone_nat_of_le_succ
    intro n ω hω
    obtain ⟨k, hk, hv⟩ := hω
    exact ⟨2 * k, by simpa only [dyadicPoint_double] using hk,
      by simpa only [dyadicPoint_double] using hv⟩
  have hAn (n : ℕ) : (ε : ℝ≥0∞) ^ 2 * μ (A n) ≤
      ENNReal.ofReal (∫ ω, M T ω ^ 2 ∂μ) := by
    let N : ℕ := ⌊(2 ^ n : ℕ) * T⌋₊
    have hp : (0 : ℝ≥0) < (2 ^ n : ℕ) := by positivity
    have hlast : dyadicPoint n N ≤ T := by
      apply (div_le_iff₀ hp).2
      simpa only [N, mul_comm] using Nat.floor_le (show (0 : ℝ≥0) ≤ ((2 ^ n : ℕ) : ℝ≥0) * T from by positivity)
    have hsub : A n ⊆ {ω | ∃ k ≤ N, (ε : ℝ) ≤ |M (dyadicPoint n k) ω|} := by
      intro ω hω
      obtain ⟨k, hk, hv⟩ := hω
      refine ⟨k, ?_, hv.le⟩
      apply Nat.le_floor
      simpa only [mul_comm] using (div_le_iff₀ hp).mp hk
    exact (mul_le_mul_right (measure_mono hsub) ((ε : ℝ≥0∞) ^ 2)).trans
      (sampled_maximal_sq hM h2 (dyadicPoint n) (dyadicPoint_mono n) ε N hlast)
  have hUnion : (ε : ℝ≥0∞) ^ 2 * μ (⋃ n, A n) ≤
      ENNReal.ofReal (∫ ω, M T ω ^ 2 ∂μ) := by
    rw [hAmono.measure_iUnion, ENNReal.mul_iSup]
    exact iSup_le hAn
  have hsub : {ω | ∃ t ≤ T, (ε : ℝ) < |M t ω|} ≤ᵐ[μ] ⋃ n, A n := by
    filter_upwards [hc] with ω hcω
    rintro ⟨t, ht, hv⟩
    have hp : Tendsto (fun n : ℕ => 2 ^ n - 1) atTop atTop :=
      (tendsto_sub_atTop_nat 1).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have hlim : Tendsto (fun n : ℕ => |M (PredictableMesh.left (2 ^ n - 1) t) ω|)
        atTop (𝓝 |M t ω|) :=
      ((hcω.tendsto t).comp ((PredictableMesh.tendsto_left t).comp hp)).abs
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 (ε : ℝ) hv).exists
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    let k := ⌈((2 ^ n - 1 + 1 : ℕ) : ℝ≥0) * t⌉₊ - 1
    have heq : dyadicPoint n k = PredictableMesh.left (2 ^ n - 1) t :=
      dyadicPoint_eq_mesh n k
    refine ⟨k, ?_, ?_⟩
    · rw [heq]
      exact (PredictableMesh.left_le _ t).trans ht
    · rw [heq]
      exact hn
  exact (mul_le_mul_right (measure_mono_ae hsub) ((ε : ℝ≥0∞) ^ 2)).trans hUnion

end Problem367.MartingaleSquareMaximal

end

end OAI
