import OAI.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition

namespace OAI

section

namespace Erdos3.FiniteProgressionPartition

open scoped BigOperators

theorem density_increment {N H : ℕ} (P : FiniteProgressionPartition N)
    (hN : 0 < N) (hH : 0 < H) (f B : ℕ → ℝ) (c : P.Label → ℝ)
    {b σ ω C : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ) (hC : 0 < C)
    (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ n < N, B n ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hω : 0 ≤ ω) (hsmall : 4 * ω ≤ σ)
    (hcount : (Fintype.card P.Label : ℝ) * H ≤ C * N)
    (hclose : ∀ i n, n < P.length i → dist (B (P.start i + P.step i * n)) (c i) ≤ ω)
    (hscore : σ ≤ 𝔼 n : Fin N, (f n.val - b) * B n.val) :
    ∃ q a len : ℕ, 0 < q ∧ σ * H / (4 * C) ≤ len ∧
      (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  let : NeZero N := ⟨hN.ne'⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hclose' (n : Fin N) : |B n.val - c (P.cell n)| ≤ ω := by
    have h := hclose (P.cell n) (P.offset n).val (P.offset n).isLt
    rw [← P.point_val, P.point_cell_offset, Real.dist_eq] at h
    exact h
  have hcost : (Fintype.card P.Label : ℝ) * (σ * H / (4 * C)) / N ≤ σ / 4 := by
    apply (div_le_iff₀ hNR).mpr
    rw [show (Fintype.card P.Label : ℝ) * (σ * H / (4 * C)) =
      ((Fintype.card P.Label : ℝ) * H * σ) / (4 * C) by ring]
    apply (div_le_iff₀ (by positivity : 0 < 4 * C)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcount hσ.le]
  obtain ⟨i, hlarge, hdense⟩ := exists_large_cell_of_normalized_score P.cell
    (fun n => f n.val) (fun n => B n.val) c (b := b) (ω := ω) (σ := σ)
    (σ * H / (4 * C)) (by positivity)
    (fun n => hf n.val n.isLt) hb (fun n => hB n.val n.isLt) hc hω hclose' hscore
    (by simp only [Fintype.card_fin]; linarith)
  refine ⟨P.step i, P.start i, P.length i, P.step_pos i, ?_, ?_, ?_⟩
  · simpa only [P.card_cell] using hlarge
  · exact fun n hn => P.point_lt i hn
  · simpa only [P.expect_cell] using hdense

end Erdos3.FiniteProgressionPartition

end

end OAI
