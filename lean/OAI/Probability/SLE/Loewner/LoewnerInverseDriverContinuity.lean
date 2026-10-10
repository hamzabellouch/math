import OAI.Probability.SLE.Loewner.LoewnerInverseCompactness

namespace OAI

/-! Uniformly close drivers give locally uniformly close inverse maps at
every fixed capacity time. This is an interior statement. -/
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

lemma inverse_maps_driver_distance
    {U V : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F H J : ℝ≥0 → ℂ → ℂ}
    (hu : IsCapacityTwoWitness U γ G F) (hv : IsCapacityTwoWitness V β H J)
    (T : ℝ≥0) {a : ℝ} (ha : 0 < a) (w : ℂ) (haw : a ≤ w.im)
    (δ : ℝ) (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) :
    dist (F T w) (J T w) ≤ gronwallBound 0 (4*a⁻¹^2) (2*a⁻¹^2*δ) T := by
  have hh := hu.inverse_approximation_bound T ha w haw V δ hUV
    (fun s => H ((T:ℝ)-s).toNNReal (J T w))
    (by simpa only [sub_zero,Real.toNNReal_coe] using hv.2.2.2.2.2.2.2.2.1 T w (ha.trans_le haw))
    (fun s hs => hv.reverse_path_derivative T w ha haw s hs)
  simpa only [sub_self,Real.toNNReal_zero,
    hv.initial_value _ (hv.2.2.2.2.2.2.1 T (ha.trans_le haw)).1.1] using hh

theorem inverse_maps_locally_uniform_of_drivers
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ) (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (h : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n))
    {V : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hUV : ∀ n t, t ∈ Icc 0 T → |U n t-V t| ≤ δ n) :
    TendstoLocallyUniformlyOn (fun n => F n T) (J T) atTop upperHalfPlane := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_upperHalfPlane]
  intro K hKH hK
  by_cases hne : K.Nonempty
  · obtain ⟨w,hw,hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
    have ha : 0 < w.im := hKH hw
    have hz : Tendsto (fun n => gronwallBound 0 (4*w.im⁻¹^2)
        (2*w.im⁻¹^2*δ n) T) atTop (𝓝 0) := by
      have hh := (gronwallBound_continuous_ε 0 (4*w.im⁻¹^2) T).continuousAt.tendsto.comp
        (hδ.const_mul (2*w.im⁻¹^2))
      simpa only [Function.comp_def,mul_zero,gronwallBound_ε0_δ0] using hh
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hz.eventually (Iio_mem_nhds hε)] with n hn z hzk
    simpa only [dist_comm] using
      (inverse_maps_driver_distance (h n) hv T ha z (hmin hzk) (δ n) (hUV n)).trans_lt hn
  · have hKe : K=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hKe,tendstoUniformlyOn_empty]

end SLEExactGauge

end

end OAI
