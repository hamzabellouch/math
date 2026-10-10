import OAI.Analysis.AncientFlat.Weighted.WeightedRescaling
import OAI.Analysis.AncientFlat.Evolution.UniformC0

namespace OAI
noncomputable section
open Set Filter Topology
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction ENNReal
namespace FlatWeighted
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma YBound.normalized_continuous {α γ a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α (-2+4*γ) a M f) (hα : 0<α) (ha : 0<a) :
    Continuous (fun p : ℝ × V => normalizedSource γ f p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × V => (Real.exp (-p.1/4) • p.2,-Real.exp (-p.1))) := by fun_prop
  exact (show Continuous (fun p : ℝ × V => Real.exp ((γ-3/2)*p.1)) by fun_prop).smul
    ((h.continuousOn hα ha).comp_continuous hc (fun p => neg_neg_of_pos (Real.exp_pos _)))
lemma YBound.normalized_pointwise {α γ a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α (-2+4*γ) a M f) (ha : 0<a) (τ : ℝ) (z : V) :
    ‖normalizedSource γ f τ z‖≤M*radius z^(-6+4*γ) := by
  rw [normalizedSource_eq_scaled]
  simpa only [show -2+4*γ-4=-6+4*γ by ring] using h.scaled_pointwise ha _ (Real.exp_pos _) z
lemma YBound.normalized_tails {α γ a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α (-2+4*γ) a M f) (hγ : γ<1/2) (ha : 0<a) :
    ∀ ε : ℝ, 0<ε → ∃ R : ℝ, ∀ τ z, R≤‖z‖ → ‖normalizedSource γ f τ z‖≤ε := by
  have ht : Tendsto (fun s : ℝ => M*s^(-6+4*γ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun s : ℝ => M*s^(-(6-4*γ))) atTop (𝓝 (M*0)) :=
      tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (show 0<6-4*γ by linarith))
    simpa only [mul_zero,show -(6-4*γ)= -6+4*γ by ring] using hh
  intro ε hε
  obtain ⟨R,hR⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨R,fun τ z hz => (h.normalized_pointwise ha τ z).trans ?_⟩
  exact (le_abs_self _).trans (by simpa only [Real.dist_eq,sub_zero] using
    (hR (radius z) (hz.trans (norm_le_radius z))).le)
lemma YBound.normalized_zero_at_infty {α γ a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α (-2+4*γ) a M f) (hγ : γ<1/2) (ha : 0<a) (τ : ℝ) :
    Tendsto (normalizedSource γ f τ) (cocompact V) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R,hR⟩ := h.normalized_tails hγ ha (ε/2) (by positivity)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop R)] with z hz
  simpa only [dist_zero_right] using (hR τ z hz).trans_lt (by linarith)
lemma YBound.normalized_bounded {α γ a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α (-2+4*γ) a M f) (hγ : γ<1/2) (ha : 0<a) (hM : 0≤M) (τ : ℝ) (z : V) :
    ‖normalizedSource γ f τ z‖≤M :=
  (h.normalized_pointwise ha τ z).trans (mul_le_of_le_one_right hM
    (Real.rpow_le_one_of_one_le_of_nonpos (one_le_radius z) (by linarith)))
lemma YBound.exists_source_bcf {α γ a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α (-2+4*γ) a M f) (hγ : γ<1/2) (hα : 0<α) (ha : 0<a) (hM : 0≤M) :
    ∃ j : ℝ →ᵇ C₀(V,ℂ), (∀ τ z, j τ z=normalizedSource γ f τ z) ∧ ‖j‖≤M := by
  let u : ℝ → C₀(V,ℂ) := fun τ =>
    ⟨⟨normalizedSource γ f τ,(h.normalized_continuous hα ha).comp
      (continuous_const.prodMk continuous_id)⟩,h.normalized_zero_at_infty hγ ha τ⟩
  have hc : Continuous u := continuous_c0_of_uniform_tails u (h.normalized_continuous hα ha)
    (h.normalized_tails hγ ha)
  have hb : ∀ τ, ‖u τ‖≤M := by
    intro τ
    change ‖(u τ).toBCF‖≤M
    exact (BoundedContinuousFunction.norm_le hM).mpr (h.normalized_bounded hγ ha hM τ)
  let j := BoundedContinuousFunction.ofNormedAddCommGroup u hc M hb
  refine ⟨j,fun _ _ => rfl,?_⟩
  exact (BoundedContinuousFunction.norm_le hM).mpr hb
end FlatWeighted

end

end OAI
