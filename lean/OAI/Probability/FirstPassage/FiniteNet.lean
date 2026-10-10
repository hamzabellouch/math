import OAI.Probability.FirstPassage.LatticeGeometry

namespace OAI

namespace PlanarFPP
open Filter Set Metric
open scoped Topology

theorem uniform_on_unit_ball_of_dense_limits
    (F : ℕ → Plane → ℝ) (μ : Plane → ℝ) (u : ℕ → Plane) (hu : DenseRange u)
    (B : ℝ) (hB : 0 < B) (hμ : ∀ v w, |μ v-μ w| ≤ B * ‖v-w‖)
    (hpoint : ∀ i, Tendsto (fun n => F n (u i)) atTop (𝓝 (μ (u i))))
    (hmod : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v w, ‖v‖ ≤ 2 → ‖w‖ ≤ 2 →
      |F n v-F n w| ≤ 8 * ‖v-w‖ + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ v, ‖v‖ ≤ 1 → |F n v-μ v| < ε := by
  intro ε hε
  let δ := min (1/2 : ℝ) (ε / (4*(8+B)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hδe : (8+B)*δ ≤ ε/4 := by
    have ht := min_le_right (1/2 : ℝ) (ε/(4*(8+B)))
    dsimp [δ]
    have hmul := (le_div_iff₀ (by linarith : 0 < 4*(8+B))).mp ht
    nlinarith
  have hcover : closedBall (0 : Plane) 1 ⊆ ⋃ i, ball (u i) δ := by
    intro v _
    obtain ⟨i, hi⟩ := hu.exists_dist_lt v hδ
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := (isCompact_closedBall (0 : Plane) 1).elim_finite_subcover
    (fun i => ball (u i) δ) (fun _ => isOpen_ball) hcover
  have hp : ∀ᶠ n in atTop, ∀ i ∈ s, |F n (u i)-μ (u i)| < ε/2 := by
    rw [eventually_all_finset]
    intro i _
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp (hpoint i) (ε/2) (by linarith))
  filter_upwards [hp, hmod (ε/4) (by linarith)] with n hn hm
  intro v hv
  obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.mp (hs (by simpa using hv))
  have hd : ‖v-u i‖ < δ := hvi
  have hui : ‖u i‖ ≤ 2 := by
    have ht := norm_sub_le (u i) v
    have ht' := norm_add_le (u i-v) v
    rw [sub_add_cancel] at ht'
    rw [norm_sub_rev] at ht'
    linarith
  have hm' := hm v (u i) (by linarith) hui
  have hμ' := hμ (u i) v
  rw [norm_sub_rev] at hμ'
  have hp' := hn i hi
  have htri : |F n v-μ v| ≤ |F n v-F n (u i)| +
      |F n (u i)-μ (u i)| + |μ (u i)-μ v| := by
    calc
      _ = |(F n v-F n (u i)) + (F n (u i)-μ (u i)) + (μ (u i)-μ v)| := by
        congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hh := mul_lt_mul_of_pos_left hd (show 0 < 8+B by linarith)
  linarith

end PlanarFPP

end OAI
