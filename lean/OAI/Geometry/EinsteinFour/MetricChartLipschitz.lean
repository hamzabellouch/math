import OAI.Geometry.EinsteinFour.MetricChartPath

namespace OAI

/-! The chart map is Lipschitz on a sufficiently small Riemannian ball.
Short paths between points of the smaller ball stay in the neighborhood
where the chart differential is bounded. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]

private theorem iInf_open_interval (a b : ℝ≥0∞) (hab : a < b) :
    (⨅ r : {r : ℝ≥0∞ // a < r ∧ r < b}, (r : ℝ≥0∞)) = a := by
  apply iInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · intro r
    exact r.property.1.le
  · intro w hw
    obtain ⟨r, har, hr⟩ := exists_between (lt_min hw hab)
    exact ⟨⟨r, har, hr.trans_le (min_le_right _ _)⟩,
      hr.trans_le (min_le_left _ _)⟩

theorem exists_metric_chart_lipschitz (g : SmoothMetric M) (c : M) :
    ∃ s ∈ 𝓝 c, s ⊆ (chartAt FourSpace c).source ∧
      ∃ K : ℝ≥0, ∀ x ∈ s, ∀ y ∈ s,
        edist (chartAt FourSpace c x) (chartAt FourSpace c y) ≤
          K * metricEDistance g x y := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  obtain ⟨K, hKpos, hK⟩ := eventually_enorm_mfderiv_extChartAt_lt I4 c
  have hK' : ∀ᶠ x in 𝓝 c,
      (let L : TangentSpace I4 x →L[ℝ] FourSpace :=
        mfderiv I4 I4 (chartAt FourSpace c) x
       ‖L‖ₑ) < K := by
    simpa only [I4, extChartAt_coe, modelWithCornersSelf_coe,
      Function.id_comp] using! hK
  let U : Set M := (chartAt FourSpace c).source ∩
    {x | (let L : TangentSpace I4 x →L[ℝ] FourSpace :=
      mfderiv I4 I4 (chartAt FourSpace c) x; ‖L‖ₑ) < K}
  have hU : U ∈ 𝓝 c := Filter.inter_mem (chart_source_mem_nhds FourSpace c) hK'
  obtain ⟨ε, hε, hεU⟩ := setOfPred_riemannianEDist_lt_subset_nhds I4 hU
  let δ : ℝ≥0 := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsum : (δ : ℝ≥0∞) + δ + δ + δ = ε := by
    exact_mod_cast (show δ + δ + δ + δ = ε by dsimp [δ]; ring)
  let s : Set M := {x | edist c x < (δ : ℝ≥0∞)}
  have hs : s ∈ 𝓝 c := by
    have hopen : IsOpen s := isOpen_lt (continuous_const.edist continuous_id) continuous_const
    exact hopen.mem_nhds (by simpa [s] using hδ)
  have hsU : s ⊆ U := by
    intro x hx
    apply hεU
    change edist c x < (ε : ℝ≥0∞)
    exact hx.trans_le (by
      calc
        (δ : ℝ≥0∞) ≤ δ + δ + δ + δ := by
          simp only [add_assoc]
          exact le_self_add
        _ = ε := hsum)
  refine ⟨s, hs, fun x hx => (hsU hx).1, K, ?_⟩
  intro x hx y hy
  have hxy : edist x y < (δ : ℝ≥0∞) + δ + δ := by
    calc
      edist x y ≤ edist c x + edist c y := edist_triangle_left _ _ _
      _ < δ + δ := ENNReal.add_lt_add hx hy
      _ ≤ δ + δ + δ := le_add_right le_rfl
  have hbound (r : {r : ℝ≥0∞ // edist x y < r ∧ r < (δ : ℝ≥0∞) + δ + δ}) :
      edist (chartAt FourSpace c x) (chartAt FourSpace c y) ≤ K * (r : ℝ≥0∞) := by
    obtain ⟨γ, hγx, hγy, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt r.property.1 zero_lt_one
    have hγU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ U := by
      apply hεU
      change edist c (γ t) < (ε : ℝ≥0∞)
      calc
        edist c (γ t) ≤ edist c x + edist x (γ t) := edist_triangle _ _ _
        _ ≤ edist c x + Manifold.pathELength I4 γ 0 t := by
          gcongr
          exact Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn hγx rfl ht.1
        _ ≤ edist c x + Manifold.pathELength I4 γ 0 1 := by
          gcongr
          exact ht.2
        _ < δ + (r : ℝ≥0∞) := ENNReal.add_lt_add hx hlen
        _ < δ + (δ + δ + δ) := ENNReal.add_lt_add_left ENNReal.coe_ne_top r.property.2
        _ = ε := by simpa only [add_assoc] using hsum
    have hchart := chart_edist_le_pathELength g c γ hγ (fun t ht => (hγU t ht).1) K
      (fun t ht v => by
        let L : TangentSpace I4 (γ t) →L[ℝ] FourSpace :=
          mfderiv I4 I4 (chartAt FourSpace c) (γ t)
        change ‖L v‖ₑ ≤ K * ‖v‖ₑ
        apply (ContinuousLinearMap.le_opENorm L v).trans
        gcongr
        exact (hγU t ht).2.le)
    rw [hγx, hγy] at hchart
    exact hchart.trans (mul_le_mul_right hlen.le _)
  change edist (chartAt FourSpace c x) (chartAt FourSpace c y) ≤ K * edist x y
  rw [← iInf_open_interval (edist x y) ((δ : ℝ≥0∞) + δ + δ) hxy,
    ENNReal.mul_iInf_of_ne (by exact_mod_cast hKpos.ne') ENNReal.coe_ne_top]
  exact le_iInf hbound

end
end PositiveEinsteinFour.Geometry

end OAI
