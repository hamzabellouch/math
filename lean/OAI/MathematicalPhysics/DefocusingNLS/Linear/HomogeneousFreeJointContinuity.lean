import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeContinuity

namespace OAI

/-! # Joint continuity of time and data for the whole-space free group -/

open Filter Topology

namespace DefocusingNLS

/-- Strong continuity and the local uniform bound give joint continuity in time and data. -/
theorem continuous_homogeneousFreeOperator_uncurry (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Continuous (fun p : ℝ × HomogeneousY a k =>
      homogeneousFreeOperator a b k p.1 ha ha1 hk p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M := homogeneousFreeBound a k p.1 + 1
  have hC : 0 < homogeneousFreeBound a k p.1 :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
  have hM : 0 < M := by dsimp [M]; linarith
  have hu : ∀ᶠ q : ℝ × HomogeneousY a k in 𝓝 p, dist q.2 p.2 < ε / (2 * M) :=
    continuous_snd.continuousAt.eventually
      (Metric.ball_mem_nhds _ (by positivity))
  have hs : ∀ᶠ q : ℝ × HomogeneousY a k in 𝓝 p,
      dist (homogeneousFreeOperator a b k q.1 ha ha1 hk p.2)
        (homogeneousFreeOperator a b k p.1 ha ha1 hk p.2) < ε / 2 :=
    (((continuous_homogeneousFreeOperator a b k ha ha1 hk p.2).comp
      continuous_fst).continuousAt).eventually (Metric.ball_mem_nhds _ (by positivity))
  have hB : ∀ᶠ q : ℝ × HomogeneousY a k in 𝓝 p,
      homogeneousFreeBound a k q.1 < M :=
    (((continuous_homogeneousFreeBound a k).comp continuous_fst).continuousAt).eventually
      (eventually_lt_nhds (by dsimp [M]; linarith))
  filter_upwards [hu, hs, hB] with q hqu hqs hqB
  have hd : dist (homogeneousFreeOperator a b k q.1 ha ha1 hk q.2)
      (homogeneousFreeOperator a b k q.1 ha ha1 hk p.2) < ε / 2 := by
    rw [dist_eq_norm, ← map_sub]
    apply (homogeneousFreeOperator_norm_le a b k q.1 ha ha1 hk (q.2 - p.2)).trans_lt
    have hm : M * (ε / (2 * M)) = ε / 2 := by field_simp
    rw [dist_eq_norm] at hqu
    have hh := mul_lt_mul_of_pos_left hqu hM
    rw [hm] at hh
    exact (mul_le_mul_of_nonneg_right hqB.le (norm_nonneg _)).trans_lt hh
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end DefocusingNLS

end OAI
