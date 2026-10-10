import OAI.Geometry.ProjectionVolume.ApproximationBounds
import OAI.Geometry.ProjectionVolume.ProjectionInterior

namespace OAI

open Set Metric Filter MeasureTheory
open scoped Pointwise Topology RealInnerProductSpace

namespace Paper092

theorem euclideanUnitBallVolume_pos (d : ℕ) : 0 < euclideanUnitBallVolume d :=
  ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_closedBall_pos volume (0 : Euclidean d) zero_lt_one))
    (isCompact_closedBall (0 : Euclidean d) 1).measure_lt_top.ne

theorem brightness_unit {d : ℕ} (K : Set (Euclidean d))
    (u : Euclidean d) (hu : ‖u‖ = 1) : brightness K u = (projectionVolume K u).toReal := by
  simp only [brightness, hu, one_mul]

theorem projectionBody_monotone_sequence {d : ℕ} {P : ℕ → Set (Euclidean d)}
    (hc : ∀ m, IsCompact (P m)) (hm : Monotone P) :
    Monotone (fun m => projectionBody (P m)) :=
  fun _ j hij => projectionBody_mono (hm hij) (hc j)

theorem approximation_projectionBody_union_closure {d : ℕ}
    {P : ℕ → Set (Euclidean d)} {K : Set (Euclidean d)}
    (hP : ∀ m, IsCompact (P m)) (hK : IsCompact K)
    {scale : ℕ → ℝ} (hscale : ∀ m, 0 < scale m) (hscalelim : Tendsto scale atTop (𝓝 1))
    (hPK : ∀ m, P m ⊆ K) (hKP : ∀ m, K ⊆ scale m • P m) :
    closure (⋃ m, projectionBody (P m)) = projectionBody K := by
  apply Subset.antisymm
  · apply closure_minimal _ (projectionBody_isClosed K)
    exact iUnion_subset fun m => projectionBody_mono (hPK m) hK
  · intro x hx
    have hq : Tendsto (fun m => scale m ^ (d - 1)) atTop (𝓝 1) := by
      have hcont : Continuous (fun x : ℝ => x ^ (d - 1)) := by fun_prop
      simpa only [Function.comp_def, one_pow] using (hcont.tendsto 1).comp hscalelim
    have hzlim : Tendsto (fun m => (scale m ^ (d - 1))⁻¹ • x) atTop (𝓝 x) := by
      have hcont : ContinuousAt (fun r : ℝ => r⁻¹ • x) 1 := by fun_prop (disch := norm_num)
      simpa only [Function.comp_def, inv_one, one_smul] using hcont.tendsto.comp hq
    apply mem_closure_of_tendsto hzlim
    apply Eventually.of_forall
    intro m
    apply mem_iUnion.mpr
    refine ⟨m, ?_⟩
    apply (mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero (d - 1) (hscale m).ne')
      (projectionBody (P m)) x).mp
    exact (approximation_projectionBody_sandwich (hP m) hK (hscale m) (hPK m) (hKP m)).2 hx

theorem approximation_support_uniform {d : ℕ} (hd : 2 ≤ d)
    {P : ℕ → Set (Euclidean d)} {K : Set (Euclidean d)}
    (hP : ∀ m, IsCompact (P m)) (hv : ∀ m, Convex ℝ (P m))
    (hi : ∀ m, (interior (P m)).Nonempty) (hK : IsCompact K)
    {scale : ℕ → ℝ} (hscale : ∀ m, 1 ≤ scale m) (hscalelim : Tendsto scale atTop (𝓝 1))
    {R : ℝ} (hR : 0 ≤ R) (hKR : K ⊆ closedBall 0 R)
    (hPK : ∀ m, P m ⊆ K) (hKP : ∀ m, K ⊆ scale m • P m) :
    TendstoUniformlyOn
      (fun m u => SupportGeometry.support (projectionBody (P m)) (innerSL ℝ u))
      (brightness K) atTop (sphere 0 1) := by
  have heq : (fun m u => SupportGeometry.support (projectionBody (P m)) (innerSL ℝ u)) =
      (fun m u => brightness (P m) u) := by
    funext m u
    exact projectionBody_support hd (P m) (hP m) (hv m) (hi m) u
  rw [heq]
  exact approximation_brightness_uniform hd hP hK hscale hscalelim hR hKR hPK hKP

theorem approximation_normalized_tendsto {d : ℕ}
    {P : ℕ → Set (Euclidean d)} {K : Set (Euclidean d)}
    (hP : ∀ m, IsCompact (P m)) (hK : IsCompact K) (hi : (interior K).Nonempty)
    {scale : ℕ → ℝ} (hscale : ∀ m, 0 < scale m) (hscalelim : Tendsto scale atTop (𝓝 1))
    (hPK : ∀ m, P m ⊆ K) (hKP : ∀ m, K ⊆ scale m • P m) :
    Tendsto (fun m => normalizedProjectionVolume (P m)) atTop
      (𝓝 (normalizedProjectionVolume K)) := by
  obtain ⟨hv, hp⟩ := approximation_volume_tendsto hP hK hscale hscalelim hPK hKP
  have hKpos : 0 < (volume K).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Measure.measure_pos_of_nonempty_interior volume hi))
      hK.measure_lt_top.ne
  exact hp.div (hv.pow (d - 1)) (pow_ne_zero _ hKpos.ne')

theorem approximation_linear_image_volume_tendsto {d : ℕ}
    {P : ℕ → Set (Euclidean d)} {K : Set (Euclidean d)}
    (hP : ∀ m, IsCompact (P m)) (hK : IsCompact K)
    {scale : ℕ → ℝ} (hscale : ∀ m, 0 < scale m) (hscalelim : Tendsto scale atTop (𝓝 1))
    (hPK : ∀ m, P m ⊆ K) (hKP : ∀ m, K ⊆ scale m • P m)
    (L : Euclidean d ≃ₗ[ℝ] Euclidean d) :
    Tendsto (fun m => (volume (L '' P m)).toReal) atTop (𝓝 (volume (L '' K)).toReal) ∧
      Tendsto (fun m => (volume (projectionBody (L '' P m))).toReal) atTop
        (𝓝 (volume (projectionBody (L '' K))).toReal) := by
  apply approximation_volume_tendsto
    (fun m => (hP m).image L.toLinearMap.continuous_of_finiteDimensional)
    (hK.image L.toLinearMap.continuous_of_finiteDimensional) hscale hscalelim
  · exact fun m => image_mono (hPK m)
  · intro m
    rw [← image_smul_comm L.toLinearMap (scale m) (P m)
      (fun x => L.toLinearMap.map_smul (scale m) x)]
    exact image_mono (hKP m)

theorem exists_projectionBody_approximating_sequence {d : ℕ} (hd : 2 ≤ d)
    {K : Set (Euclidean d)} (hK : IsCompact K) (hv : Convex ℝ K)
    (h0 : (0 : Euclidean d) ∈ interior K) :
    ∃ (V : ℕ → Finset (Euclidean d)) (a R : ℝ),
      let P := fun m => convexHull ℝ (V m : Set (Euclidean d))
      let ε := fun m : ℕ => R / ((m : ℝ) + 2)
      let scale := fun m => 1 + ε m / a
      0 < a ∧ 0 < R ∧ K ⊆ closedBall 0 R ∧ Monotone P ∧
      (∀ m, closedBall (0 : Euclidean d) a ⊆ P m ∧ P m ⊆ K ∧
        K ⊆ P m + closedBall 0 (ε m) ∧ P m + closedBall 0 (ε m) ⊆ scale m • P m) ∧
      Tendsto ε atTop (𝓝 0) ∧
      TendstoUniformlyOn
        (fun m u => SupportGeometry.support (projectionBody (P m)) (innerSL ℝ u))
        (brightness K) atTop (sphere 0 1) ∧
      (∀ m, closedBall (0 : Euclidean d)
          (euclideanUnitBallVolume (d - 1) * a ^ (d - 1)) ⊆ projectionBody (P m) ∧
        projectionBody (P m) ⊆ closedBall 0
          (euclideanUnitBallVolume (d - 1) * R ^ (d - 1))) ∧
      closure (⋃ m, projectionBody (P m)) = projectionBody K ∧
      (∀ m, (volume (P m)).toReal ≤ (volume K).toReal ∧
        (volume K).toReal ≤ scale m ^ d * (volume (P m)).toReal ∧
        (volume (projectionBody (P m))).toReal ≤ (volume (projectionBody K)).toReal ∧
        (volume (projectionBody K)).toReal ≤
          scale m ^ (d * (d - 1)) * (volume (projectionBody (P m))).toReal) ∧
      Tendsto (fun m => (volume (P m)).toReal) atTop (𝓝 (volume K).toReal) ∧
      Tendsto (fun m => (volume (projectionBody (P m))).toReal) atTop
        (𝓝 (volume (projectionBody K)).toReal) := by
  obtain ⟨V, a, R, ha, hR, hKR, hmono, hball, hsand, heps⟩ :=
    exists_inscribed_polytope_sequence hK hv h0
  let P := fun m => convexHull ℝ (V m : Set (Euclidean d))
  let ε := fun m : ℕ => R / ((m : ℝ) + 2)
  let scale := fun m => 1 + ε m / a
  have hc : ∀ m, IsCompact (P m) := fun m => (V m).finite_toSet.isCompact_convexHull ℝ
  have hvP : ∀ m, Convex ℝ (P m) := fun _ => convex_convexHull ℝ _
  have hiP : ∀ m, (interior (P m)).Nonempty := fun m =>
    ⟨0, interior_mono (hball m) (ball_subset_interior_closedBall (mem_ball_self ha))⟩
  have hPK : ∀ m, P m ⊆ K := fun m => (hsand m).1
  have hKP : ∀ m, K ⊆ scale m • P m := fun m => (hsand m).2.1.trans (hsand m).2.2
  have hscale : ∀ m, 1 ≤ scale m := by
    intro m
    dsimp [scale, ε]
    exact le_add_of_nonneg_right (by positivity)
  have hscalepos : ∀ m, 0 < scale m := fun m => zero_lt_one.trans_le (hscale m)
  have hscalelim : Tendsto scale atTop (𝓝 1) := by
    have hcont : Continuous (fun x : ℝ => 1 + x / a) := by fun_prop
    simpa only [Function.comp_def, zero_div, add_zero] using (hcont.tendsto 0).comp heps
  obtain ⟨hvol, hpivol⟩ := approximation_volume_tendsto hc hK hscalepos hscalelim hPK hKP
  refine ⟨V, a, R, ha, hR, hKR, hmono, ?_, heps, ?_, ?_, ?_, ?_, hvol, hpivol⟩
  · exact fun m => ⟨hball m, (hsand m).1, (hsand m).2⟩
  · exact approximation_support_uniform hd hc hvP hiP hK hscale hscalelim hR.le hKR hPK hKP
  · intro m
    exact ⟨ball_subset_projectionBody hd (hc m) ha.le (hball m),
      projectionBody_subset_ball hd hR.le ((hPK m).trans hKR)⟩
  · exact approximation_projectionBody_union_closure hc hK hscalepos hscalelim hPK hKP
  · intro m
    have hbody := approximation_volume_sandwich (hc m) hK (hscalepos m).le (hPK m) (hKP m)
    have hpi := approximation_projectionBody_volume_sandwich (hc m) hK (hscalepos m) (hPK m) (hKP m)
    exact ⟨hbody.1, hbody.2, hpi⟩

end Paper092

end OAI
