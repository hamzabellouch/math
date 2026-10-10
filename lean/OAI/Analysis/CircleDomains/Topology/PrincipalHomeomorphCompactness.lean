import OAI.Analysis.CircleDomains.Topology.PrincipalHomeomorphBounds
import OAI.Geometry.Cannon.Topology.CenteredHomeomorph

namespace OAI

/-! A common exterior principal bound gives compactness of the maps and
inverses directly. The limits keep the original principal scale. -/
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonPlane

lemma principal_smooth_homeomorph_subsequence (F : ℕ → ℂ ≃ₜ ℂ)
    (hF : ∀ n, ContDiff ℝ 1 (F n : ℂ → ℂ))
    (hFi : ∀ n, ContDiff ℝ 1 ((F n).symm : ℂ → ℂ))
    {K R : ℝ} (hK : 0 ≤ K) (hR : 0 < R)
    (hD : ∀ n z, ‖fderiv ℝ (F n : ℂ → ℂ) z‖^2 ≤
      K*|(fderiv ℝ (F n : ℂ → ℂ) z).det|)
    (hDi : ∀ n z, ‖fderiv ℝ ((F n).symm : ℂ → ℂ) z‖^2 ≤
      K*|(fderiv ℝ ((F n).symm : ℂ → ℂ) z).det|)
    (hb : ∀ n z, 2*R ≤ ‖z‖ → ‖F n z-z‖ ≤ R) :
    ∃ H : ℂ ≃ₜ ℂ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => homeomorphMap (F (σ n))) atTop (𝓝 (homeomorphMap H)) ∧
      Tendsto (fun n => homeomorphMap (F (σ n)).symm) atTop
        (𝓝 (homeomorphMap H.symm)) := by
  have hr : UniformRelativeControl (fun n z => F n z) := by
    intro ε hε
    obtain ⟨η, hη, h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η, hη, fun n => h (F n) (hFi n) (hDi n)⟩
  have hri : UniformRelativeControl (fun n z => (F n).symm z) := by
    intro ε hε
    obtain ⟨η, hη, h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η, hη, fun n => h (F n).symm (hF n) (hD n)⟩
  have hbounds := fun n => principal_homeomorph_pointwise_bounds (F n) hR (hb n)
  have hbf : ∀ z, ∃ B, ∀ n, ‖F n z‖ ≤ B :=
    fun z => ⟨max (3*R) (‖z‖+R), fun n => (hbounds n).1 z⟩
  have hbi : ∀ z, ∃ B, ∀ n, ‖(F n).symm z‖ ≤ B :=
    fun z => ⟨max (2*R) (‖z‖+R), fun n => (hbounds n).2 z⟩
  exact pointwise_bounded_homeomorph_subsequence F
    (relative_control_equicontinuous _ hr hbf)
    (relative_control_equicontinuous _ hri hbi) hbf hbi

lemma principal_limit_decay {F : ℕ → ℂ → ℂ} {H : ℂ → ℂ} {R : ℝ}
    (hlim : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (H z)))
    (hb : ∀ n z, 2*R ≤ ‖z‖ → ‖F n z-z‖ ≤ 2*R^2/‖z‖) :
    Tendsto (fun z => H z-z) (Bornology.cobounded ℂ) (𝓝 0) := by
  have hbound (z : ℂ) (hz : 2*R ≤ ‖z‖) : ‖H z-z‖ ≤ 2*R^2/‖z‖ :=
    le_of_tendsto ((hlim z).sub_const z |>.norm) (.of_forall (fun n => hb n z hz))
  apply squeeze_zero_norm' (a := fun z : ℂ => 2*R^2/‖z‖) ?_ ?_
  · filter_upwards [eventually_cobounded_le_norm (2*R)] with z hz
    exact hbound z hz
  · simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_norm_cobounded_atTop) :
        Tendsto (fun z : ℂ => (2*R^2)*‖z‖⁻¹) (Bornology.cobounded ℂ) (𝓝 ((2*R^2)*0)))

end CircleDomainRigidity

end

end OAI
