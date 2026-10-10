import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedComplement
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarMultiwellScale
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalCappedScale

namespace OAI

/-! Fixed localization parameters for the manufactured one-electron gap.
The number of sites enters only through the proved exponential count bound. -/

noncomputable section
open Filter
open scoped Topology
namespace ContinuumCoulomb

theorem planar_projection_loss_threshold {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ R : ℝ, 8 ≤ R ∧ ∀ D : ℝ, R ≤ D → ∀ m : ℕ,
      (m : ℝ) ≤ Real.exp ((19/320:ℝ)*D) →
      planarSiteDerivativeBound D^2+
        γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)) ≤ ε := by
  have hexp : Tendsto (fun D : ℝ => Real.exp (-(19/320:ℝ)*D)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<19/320))
  have hl : Tendsto (fun D : ℝ => planarSiteDerivativeBound D^2+
      γ*(1+η⁻¹)*planarSiteTailConstant*Real.exp (-(19/320:ℝ)*D)) atTop (𝓝 0) := by
    simpa using (planarSiteDerivativeBound_tendsto.pow 2).add
      (hexp.const_mul (γ*(1+η⁻¹)*planarSiteTailConstant))
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.1 (hl.eventually (gt_mem_nhds hε))
  refine ⟨max 8 R,le_max_left _ _,fun D hD m hm => ?_⟩
  have hC : 0 ≤ γ*(1+η⁻¹)*planarSiteTailConstant := by
    exact mul_nonneg (mul_nonneg hγ.le (by positivity)) planarSiteTailConstant_nonnegative
  have ht : γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)) ≤
      γ*(1+η⁻¹)*planarSiteTailConstant*Real.exp (-(19/320:ℝ)*D) := by
    calc
      _ = (γ*(1+η⁻¹)*planarSiteTailConstant)*
        ((m:ℝ)*Real.exp (-(19/20:ℝ)*(D/8))) := by ring
      _ ≤ (γ*(1+η⁻¹)*planarSiteTailConstant)*
        (Real.exp ((19/320:ℝ)*D)*Real.exp (-(19/20:ℝ)*(D/8))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le) hC
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  exact (add_le_add le_rfl ht).trans (hR D ((le_max_right _ _).trans hD)).le

theorem vertical_projection_loss_tendsto {freq : ℝ} (hfreq : 0 < freq) (η : ℝ) :
    Tendsto (fun S : ℝ => verticalCutoffDerivativeBound S^2/2+
      freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) atTop (𝓝 0) := by
  have harg : Tendsto (fun S : ℝ => (freq/8)*S^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop (by positivity : 0 < freq/8)
  have he : Tendsto (fun S : ℝ => Real.exp (-freq*S^2/8)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp harg using 1
    ext S
    congr 1
    ring
  simpa using ((verticalCutoffDerivativeBound_tendsto.pow 2).div_const 2).add
    (he.const_mul (freq*(1+η⁻¹)*verticalCutoffTailConstant freq))

theorem vertical_projection_loss_threshold {freq ε : ℝ}
    (hfreq : 0 < freq) (η : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ S : ℝ, R ≤ S →
      3*freq/2 ≤ freq^2*S^2/8 ∧
      verticalCutoffDerivativeBound S^2/2+
        freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8) ≤ ε := by
  have hbar : Tendsto (fun S : ℝ => (freq^2/8)*S^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop (by positivity : 0 < freq^2/8)
  have hb : ∀ᶠ S : ℝ in atTop, 3*freq/2 ≤ freq^2*S^2/8 := by
    filter_upwards [hbar.eventually (eventually_ge_atTop (3*freq/2))] with S hS
    convert hS using 1
    ring
  have hl := (vertical_projection_loss_tendsto hfreq η).eventually (gt_mem_nhds hε)
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.1 (hb.and hl)
  refine ⟨max 1 R,le_max_left _ _,fun S hS => ?_⟩
  obtain ⟨hb,hl⟩ := hR S ((le_max_right _ _).trans hS)
  exact ⟨hb,hl.le⟩

theorem manufactured_gap_parameter_bounds {γ freq : ℝ}
    (hγ : 0 < γ) (hsmall : γ ≤ 1/4) (hfreq : 1 ≤ freq) :
    0 < γ/(16*freq) ∧ freq*(γ/(16*freq)) = γ/16 ∧
      ∀ t : ℝ, t ≤ 1/2 →
        γ*(1+γ/(16*freq))*(1+t) ≤ freq*(1+γ/(16*freq)) := by
  have hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
  have hη : 0 < γ/(16*freq) := by positivity
  refine ⟨hη,by field_simp,fun t ht => ?_⟩
  have hgt : γ*(1+t) ≤ freq := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hgt (show 0 ≤ 1+γ/(16*freq) by positivity)
  nlinarith only [hh]

end ContinuumCoulomb

end

end OAI
