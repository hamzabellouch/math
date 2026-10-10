import OAI.Geometry.NodalSets.Elliptic.SmoothCutoff

namespace OAI

namespace Yau.Waves
open Filter
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma scaledCutoff_derivative_zero_near {N : ℝ} (hN : 0 < N) (y x : E)
    {k : ℕ} (hk : k ≠ 0) (hx : ‖x - y‖ < N ^ (-1 / 3 : ℝ)) :
    iteratedFDeriv ℝ k (scaledCutoff N y) x = 0 := by
  have hball : N ^ (1 / 3 : ℝ) • (x - y) ∈ Metric.ball (0 : E) (baseCutoff (E := E)).rIn := by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hN _)]
    change N ^ (1 / 3 : ℝ) * ‖x - y‖ < 1
    calc
      _ < N ^ (1 / 3 : ℝ) * N ^ (-1 / 3 : ℝ) :=
        mul_lt_mul_of_pos_left hx (Real.rpow_pos_of_pos hN _)
      _ = 1 := by rw [← Real.rpow_add hN]; norm_num
  have h := ((baseCutoff (E := E)).eventuallyEq_one_of_mem_ball hball).iteratedFDeriv ℝ k
  have he := h.self_of_nhds
  have hz : iteratedFDeriv ℝ k (fun _ : E ↦ (1 : ℝ)) = 0 := iteratedFDeriv_const_of_ne hk 1
  change iteratedFDeriv ℝ k (baseCutoff (E := E)) _ =
    iteratedFDeriv ℝ k (fun _ : E ↦ (1 : ℝ)) _ at he
  rw [hz] at he
  change iteratedFDeriv ℝ k (fun z ↦ (baseCutoff (E := E)) (N ^ (1 / 3 : ℝ) • (z - y))) x = 0
  rw [iteratedFDeriv_dilate_translate (baseCutoff (E := E)).contDiff, he]
  simp

theorem scaledCutoff_derivative_annulus {N : ℝ} (hN : 0 < N) (y x : E)
    {k : ℕ} (hk : k ≠ 0) (hd : iteratedFDeriv ℝ k (scaledCutoff N y) x ≠ 0) :
    N ^ (1 / 3 : ℝ) ≤ N * ‖x - y‖ ^ 2 := by
  have hr : N ^ (-1 / 3 : ℝ) ≤ ‖x - y‖ := by
    by_contra h
    exact hd (scaledCutoff_derivative_zero_near hN y x hk (lt_of_not_ge h))
  have he : N * (N ^ (-1 / 3 : ℝ)) ^ 2 = N ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    nth_rw 1 [← Real.rpow_one N]
    rw [← Real.rpow_add hN]
    congr 1
    norm_num
  rw [← he]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hr 2) hN.le

theorem differentiated_cutoff_gaussian_bound (c : ℝ) (hc : 0 < c)
    (p K : ℝ) (k : ℕ) (hk : k ≠ 0) :
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ y x : E, ∀ S A : ℝ, 0 ≤ A →
      ‖iteratedFDeriv ℝ k (scaledCutoff N y) x‖ * A * N ^ p *
        Real.exp (N * S - c * N * ‖x - y‖ ^ 2) ≤
      C * A * N ^ (-K) * Real.exp (N * S) := by
  obtain ⟨C, hC, hD⟩ := scaledCutoff_derivative_bound (E := E) k
  refine ⟨C, hC, ?_⟩
  filter_upwards [gaussian_cutoff_bound c 1 hc (by norm_num) ((k : ℝ) / 3 + p) K,
    eventually_gt_atTop (0 : ℝ)] with N hgauss hN
  intro y x S A hA
  by_cases hd : iteratedFDeriv ℝ k (scaledCutoff N y) x = 0
  · rw [hd, norm_zero, zero_mul, zero_mul, zero_mul]
    positivity
  · have hg := hgauss S ‖x - y‖ (C * A) (mul_nonneg hC.le hA)
      (by simpa using scaledCutoff_derivative_annulus hN y x hk hd)
    calc
      _ ≤ (C * N ^ ((k : ℝ) / 3)) * A * N ^ p *
          Real.exp (N * S - c * N * ‖x - y‖ ^ 2) := by
        gcongr
        exact hD N hN y x
      _ = (C * A) * N ^ ((k : ℝ) / 3 + p) *
          Real.exp (N * S - c * N * ‖x - y‖ ^ 2) := by
        rw [Real.rpow_add hN]
        ring
      _ ≤ _ := hg

end
end Yau.Waves

end OAI
