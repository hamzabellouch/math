import OAI.Probability.SLE.Loewner.SlitChartDisplacement
import OAI.Probability.SLE.Loewner.InitialCapacityAtZero

namespace OAI

/-! The actual normalized inverse charts of initial subarcs start at the identity. -/
noncomputable section
open Set Filter Function Metric
open scoped Topology

namespace SLEExactGauge

noncomputable def initialInverseChart (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) : ℂ → ℂ :=
  if ht : t=0 then id else (initialSlitChart p hi h0 hH t ht).inverse

@[simp] lemma initialInverseChart_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    initialInverseChart p hi h0 hH 0=id := by simp [initialInverseChart]

lemma initialInverseChart_differentiableOn (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) : DifferentiableOn ℂ (initialInverseChart p hi h0 hH t) upperHalfPlane := by
  by_cases ht : t=0
  · simp only [ht,initialInverseChart_zero]
    exact differentiableOn_id
  · rw [initialInverseChart,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).inverse_differentiable

lemma initialInverseChart_displacement (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane) :
    ‖initialInverseChart p hi h0 hH t z-z‖≤ initialCapacity p hi h0 hH t/z.im := by
  by_cases ht : t=0
  · simp [ht]
  · rw [initialInverseChart,dite_eq_right ht,initialCapacity,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).inverse_displacement hz

lemma compact_upperHalfPlane_min_height {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ upperHalfPlane) (hne : K.Nonempty) :
    ∃ m : ℝ, 0< m ∧ ∀ z∈K, m≤ z.im := by
  obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  exact ⟨z.im,hKH hz,fun w hw => hmin hw⟩

theorem initialInverseChart_tendsto_identity (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    TendstoLocallyUniformlyOn (initialInverseChart p hi h0 hH) id (𝓝 0) upperHalfPlane := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_upperHalfPlane]
  intro K hKH hK
  by_cases hne : K.Nonempty
  · obtain ⟨m,hm,hmin⟩ := compact_upperHalfPlane_min_height hK hKH hne
    have hcap : Tendsto (initialCapacity p hi h0 hH) (𝓝 0) (𝓝 0) := by
      simpa only [initialCapacity_zero] using (initialCapacity_continuousAt_zero p hi h0 hH).tendsto
    have hsmall : Tendsto (fun t => initialCapacity p hi h0 hH t/m) (𝓝 0) (𝓝 0) := by
      simpa only [zero_div] using hcap.div_const m
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with t ht
    intro z hz
    rw [dist_eq_norm,show id z=z from rfl,norm_sub_rev]
    exact ((initialInverseChart_displacement p hi h0 hH t (hKH hz)).trans
      (div_le_div_of_nonneg_left (initialCapacity_nonneg p hi h0 hH t) hm (hmin z hz))).trans_lt ht
  · simpa only [not_nonempty_iff_eq_empty.mp hne] using
      (tendstoUniformlyOn_empty : TendstoUniformlyOn (initialInverseChart p hi h0 hH) id (𝓝 0) ∅)

end SLEExactGauge

end

end OAI
