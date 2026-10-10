import OAI.Probability.SLE.Gauge.PrescribedRadiusLevels

namespace OAI

/-! Uniform control of the prescribed logarithmic levels on a compact
subset of the open half-plane. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge.Target

lemma continuous_entryPhysicalLevel (κ : ℝ) (W : WienerLaw) (e : Entry)
    {A : ℝ} (hA : 0<A) :
    Continuous (fun z : upperHalfPlane => entryPhysicalLevel κ W e A z) := by
  have hf : Continuous (fun z : upperHalfPlane => (2*(z:ℂ).im)/A) := by fun_prop
  have hn (z : upperHalfPlane) : (2*(z:ℂ).im)/A ≠ 0 :=
    ne_of_gt (div_pos (mul_pos (by norm_num) z.property) hA)
  exact ((hf.log hn).add continuous_const).add continuous_const

lemma entryPhysicalLevel_bounded_on_compact (κ : ℝ) (W : WienerLaw) (e : Entry)
    {A : ℝ} (hA : 0<A) (K : Set upperHalfPlane) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ z∈K, entryPhysicalLevel κ W e A z ≤ M := by
  obtain ⟨M,hM⟩ := hK.bddAbove_image
    (continuous_entryPhysicalLevel κ W e hA).continuousOn
  exact ⟨M,fun z hz => hM ⟨z,hz,rfl⟩⟩

lemma eventually_entryPhysicalLevel_large_on_compact {κ : ℝ} (hκ : 0<κ)
    (W : WienerLaw) {A : ℝ} (hA : 0<A) (L : ℝ)
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    ∃ N : ℕ, ∀ e : GaugeIndex κ W, N≤e.val.1 → ∀ z∈K,
      L<entryPhysicalLevel κ W e.val A z := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0,by simp⟩
  obtain ⟨z₀,hz₀,hmin⟩ := hK.exists_isMinOn hne
    (Complex.continuous_im.comp continuous_subtype_val).continuousOn
  have he : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hh : ∀ᶠ n : ℕ in atTop, Real.exp (-(n:ℝ)) < (z₀:ℂ).im :=
    he.eventually (gt_mem_nhds z₀.property)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (hh.and (eventually_entryPhysicalLevel_large hκ W hA L))
  refine ⟨N,?_⟩
  intro e he z hz
  exact (hN e.val.1 he).2 e.val.2 z
    ((hN e.val.1 he).1.le.trans (hmin hz))

end SLEExactGauge.Target

end

end OAI
