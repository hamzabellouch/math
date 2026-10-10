import OAI.Probability.SLE.Loewner.RealBoundaryDriverNeighborhood

namespace OAI

/-! A regular real characteristic excludes an entire neighborhood from
the perturbed trace, including its real boundary points. -/
noncomputable section
open Set Filter Complex Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem real_boundary_driver_trace_avoidance
    (V : ℝ≥0 → ℝ) (T : ℝ≥0) (q : ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hgap : ∀ t ∈ Icc 0 (T : ℝ), m ≤ q t-V t.toNNReal)
    (hqd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt q
      (2/(q t-V t.toNNReal)) (Icc 0 (T : ℝ)) t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (U : ℝ≥0 → ℝ), Continuous U →
      ∀ (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t-V t| ≤ ε) →
      ∀ t ∈ Icc 0 T, γ t ∉ ball ((q 0 : ℝ) : ℂ) ε := by
  obtain ⟨δ,hδ,hcontrol⟩ := real_boundary_driver_neighborhood_control V T q hm hgap hqd
  let ε := min δ (m/4)
  have hε : 0 < ε := lt_min hδ (by positivity)
  refine ⟨ε,hε,?_⟩
  intro U hU γ G F hw hUV t ht hball
  have hUVδ : ∀ s ∈ Icc 0 T, |U s-V s| ≤ δ :=
    fun s hs => (hUV s hs).trans (min_le_left _ _)
  have hballδ : γ t ∈ ball ((q 0 : ℝ) : ℂ) δ :=
    (ball_subset_ball (min_le_left _ _)) hball
  have hnear : ∀ᶠ y : ℝ in 𝓝[>] 0,
      F t ((U t : ℂ)+(y : ℂ)*I) ∈ ball ((q 0 : ℝ) : ℂ) δ :=
    (hw.2.2.2.2.2.2.2.2.2.2.2.2 t).eventually (isOpen_ball.mem_nhds hballδ)
  have he : ∀ᶠ y : ℝ in 𝓝[>] 0,
      dist ((U t : ℂ)+(y : ℂ)*I) (q t : ℂ) ≤ m/4 := by
    filter_upwards [hnear,self_mem_nhdsWithin] with y hy hy0
    have hwH : (U t : ℂ)+(y : ℂ)*I ∈ upperHalfPlane := by
      simpa [upperHalfPlane] using hy0
    have hzH := (hw.2.2.2.2.2.2.1 t hwH).1.1
    have hh := (hcontrol U hU γ G F hw hUVδ _ ⟨hy,hzH⟩).2 t ht.2
    rw [hw.2.2.2.2.2.2.2.2.1 t _ hwH] at hh
    exact hh.le
  have hd : Tendsto (fun y : ℝ => dist ((U t : ℂ)+(y : ℂ)*I) (q t : ℂ))
      (𝓝[>] 0) (𝓝 (dist (U t : ℂ) (q t : ℂ))) := by
    have hc : Continuous (fun y : ℝ => dist ((U t : ℂ)+(y : ℂ)*I) (q t : ℂ)) := by fun_prop
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hb := le_of_tendsto hd he
  have hr : |U t-q t| ≤ m/4 := by
    simpa only [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hb
  have hg : m ≤ q t-V t := by
    simpa only [Real.toNNReal_coe] using hgap t ⟨t.coe_nonneg,by exact_mod_cast ht.2⟩
  have hu : |U t-V t| ≤ m/4 := (hUV t ht).trans (min_le_right _ _)
  linarith [(abs_le.mp hr).1,(abs_le.mp hu).2]

end SLEExactGauge

end

end OAI
