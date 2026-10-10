import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialPotentialSqrtDeriv
import OAI.Analysis.CoulombIonization.Variational.SpatialRotation
import OAI.Analysis.CoulombIonization.Localization.RadialPacket
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchCoulombControl

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SmoothNewton_scope

open MeasureTheory Filter Set Metric InnerProductSpace Laplacian
open scoped ContDiff BigOperators Convolution

namespace CoulombAnalysis

lemma newtonInverse_locallyIntegrable :
    LocallyIntegrable (fun x : TFSpace => ‖x‖⁻¹) := by
  apply locallyIntegrable_of_norm_le_rpow (C := (1:ℝ)) (α := (1:ℝ))
    (by simp [TFSpace]) (by simp [TFSpace])
  · exact Eventually.of_forall fun x => by simp [Real.rpow_neg_one]
  · exact measurable_norm.inv.aestronglyMeasurable

lemma tfPotential_eq_convolution (ρ : TFSpace → ℝ) :
    tfPotential ρ = ρ ⋆[newtonMul] (fun x : TFSpace => ‖x‖⁻¹) := by
  funext x
  simp only [tfPotential,convolution,newtonMul,ContinuousLinearMap.mul_apply',div_eq_mul_inv]

lemma tfPotential_contDiff {ρ : TFSpace → ℝ} {n : ℕ∞}
    (hρ : ContDiff ℝ n ρ) (hc : HasCompactSupport ρ) :
    ContDiff ℝ n (tfPotential ρ) := by
  rw [tfPotential_eq_convolution]
  exact hc.contDiff_convolution_left newtonMul hρ newtonInverse_locallyIntegrable

lemma tfPotential_poisson_global {ρ : TFSpace → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hc : HasCompactSupport ρ) (hr : IsRadial ρ) :
    Δ (tfPotential ρ) = fun x => -(4*Real.pi*ρ x) := by
  obtain ⟨R,hR,hRs⟩ := hc.isCompact.isBounded.exists_pos_norm_lt
  have hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R := fun y hy =>
    (hRs y (subset_tsupport ρ hy)).le
  apply Measure.eq_of_ae_eq (μ := volume) _ (tfLaplacian_continuous (tfPotential_contDiff hρ hc))
    ((continuous_const.mul hρ.continuous).neg)
  filter_upwards [CoulombAtom.ae_ne_point (0 : TFSpace)] with x hx
  exact (tfPotential_poisson (hρ.continuous.integrable_of_hasCompactSupport hc)
    (hρ.continuous.memLp_of_hasCompactSupport hc) hr (fun _ _ => hρ.continuous.continuousAt)
    hR.le hs hx).2

lemma tfLaplacian_translate (f : TFSpace → ℝ) (a : TFSpace) :
    Δ (fun x => f (a+x)) = fun x => Δ f (a+x) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,iteratedFDeriv_comp_add_left]

end CoulombAnalysis
namespace CoulombAtom

lemma packetDensity_smooth (y : Space) (R : ℝ) :
    ContDiff ℝ ∞ (packetDensity y R) := by
  have hc : ContDiff ℝ ∞ (fun x : Space => R⁻¹ • (x-y)) :=
    (contDiff_id.sub contDiff_const).const_smul R⁻¹
  have hn := (radialPacketBase_smooth.comp hc).norm_sq ℝ
  change ContDiff ℝ ∞ (fun x : Space => packetDensity y R x)
  simp_rw [packetDensity_formula]
  exact contDiff_const.mul hn

end CoulombAtom

end Work_SmoothNewton_scope

open MeasureTheory Filter Set Metric InnerProductSpace Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis

lemma shrinking_density_test_limit {η : ℕ → TFSpace → ℝ} {r : ℕ → ℝ}
    (hc : ∀ n, Continuous (η n)) (hcompact : ∀ n, HasCompactSupport (η n))
    (hn : ∀ n x, 0 ≤ η n x) (hm : ∀ n, ∫ x, η n x = 1)
    (hs : ∀ n x, η n x ≠ 0 → ‖x‖ ≤ r n) (hr : Tendsto r atTop (𝓝 0))
    {g : TFSpace → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ x, η n x*g x) atTop (𝓝 (g 0)) := by
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨d,hd,heps⟩ := (Metric.continuousAt_iff.mp hg.continuousAt) (e/2) (half_pos he)
  filter_upwards [hr.eventually (gt_mem_nhds hd)] with n hnsmall
  have hi : Integrable (η n) := (hc n).integrable_of_hasCompactSupport (hcompact n)
  have hi2 : Integrable (fun x => η n x*g x) := ((hc n).mul hg).integrable_of_hasCompactSupport (hcompact n).mul_right
  have heq : (∫ x, η n x*g x)-g 0 = ∫ x, η n x*(g x-g 0) := by
    simp_rw [mul_sub]
    rw [integral_sub hi2 (hi.mul_const _),integral_mul_const,hm,one_mul]
  have hb : ‖∫ x, η n x*(g x-g 0)‖ ≤ e/2 := by
    have hh := norm_integral_le_of_norm_le (hi.const_mul (e/2))
      (Eventually.of_forall fun x => (show ‖η n x*(g x-g 0)‖ ≤ (e/2)*η n x from by
        by_cases hx : η n x = 0
        · simp [hx]
        · rw [norm_mul,Real.norm_of_nonneg (hn n x),Real.norm_eq_abs]
          have hgx : |g x-g 0| < e/2 := by
            apply heps
            simpa only [dist_zero_right] using (hs n x hx).trans_lt hnsmall
          nlinarith [mul_le_mul_of_nonneg_left hgx.le (hn n x)]))
    simpa only [integral_const_mul,hm,mul_one] using hh
  rw [dist_eq_norm,heq]
  exact hb.trans_lt (half_lt_self he)

lemma radial_mollifier_laplacian_identity {η : ℕ → TFSpace → ℝ} {r : ℕ → ℝ}
    (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop (𝓝 0))
    (hc : ∀ n, ContDiff ℝ 2 (η n)) (hcompact : ∀ n, HasCompactSupport (η n))
    (hn : ∀ n x, 0 ≤ η n x) (hm : ∀ n, ∫ x, η n x = 1)
    (hs : ∀ n x, η n x ≠ 0 → ‖x‖ ≤ r n) (hrad : ∀ n, IsRadial (η n))
    {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, Δ g x/‖x‖) = -(4*Real.pi*g 0) := by
  have hi (n : ℕ) : Integrable (η n) := (hc n).continuous.integrable_of_hasCompactSupport (hcompact n)
  have hp (n : ℕ) : MemLp (η n) (5/3) :=
    (hc n).continuous.memLp_of_hasCompactSupport (hcompact n)
  have hdl := tfLaplacian_continuous hg
  have hdcomp := tfLaplacian_compact hg hcg
  have hbound : Integrable (fun x : TFSpace => |Δ g x|/‖x‖) := by
    simpa only [zero_sub,norm_neg,Real.norm_eq_abs,abs_div,abs_norm] using
      (tfPotential_integrable (hdl.integrable_of_hasCompactSupport hdcomp)
        (hdl.memLp_of_hasCompactSupport hdcomp) 0).norm
  have hlim : Tendsto (fun n => ∫ x, tfPotential (η n) x*Δ g x) atTop
      (𝓝 (∫ x, Δ g x/‖x‖)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |Δ g x|/‖x‖)
    · intro n
      exact (((tfPotential_contDiff (hc n) (hcompact n)).continuous).mul hdl).aestronglyMeasurable
    · exact hbound
    · intro n
      filter_upwards [CoulombAtom.ae_ne_point (0 : TFSpace)] with x hx
      rw [norm_mul,Real.norm_of_nonneg (tfPotential_nonneg (Eventually.of_forall (hn n)) x),
        Real.norm_eq_abs]
      have hb := CoulombAtom.radial_potential_le_point (hi n) (hp n) (hn n) (hrad n)
        (hrpos n).le (hs n) hx
      rw [hm] at hb
      have hh := mul_le_mul_of_nonneg_right hb (abs_nonneg (Δ g x))
      simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
    · filter_upwards [CoulombAtom.ae_ne_point (0 : TFSpace)] with x hx
      have hsmall := hr.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))
      apply tendsto_const_nhds.congr'
      filter_upwards [hsmall] with n hnx
      rw [tfPotential_newton_exterior_closed (hi n) (hp n) (hrad n) (hrpos n) (hs n) hnx.le,hm]
      ring
  have hright := (shrinking_density_test_limit (fun n => (hc n).continuous) hcompact hn hm hs hr
    hg.continuous).const_mul (-(4*Real.pi))
  have he (n : ℕ) : (∫ x, tfPotential (η n) x*Δ g x) =
      -(4*Real.pi)*(∫ x, η n x*g x) := by
    rw [compact_laplacian_green (tfPotential_contDiff (hc n) (hcompact n)) hg hcg,
      tfPotential_poisson_global (hc n) (hcompact n) (hrad n)]
    calc
      _ = ∫ x, -(4*Real.pi)*(η n x*g x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := integral_const_mul _ _
  have hh := tendsto_nhds_unique hlim (hright.congr (fun n => (he n).symm))
  simpa only [neg_mul] using hh

theorem compact_laplacian_newton_zero {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, Δ g x/‖x‖) = -(4*Real.pi*g 0) := by
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply radial_mollifier_laplacian_identity (η := fun n => CoulombAtom.packetDensity 0 (r n)) hrpos hr
    (fun n => (CoulombAtom.packetDensity_smooth 0 (r n)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (fun n => CoulombAtom.packetDensity_compact 0 (hrpos n))
    (fun n => CoulombAtom.packetDensity_nonneg 0 (r n))
    (fun n => CoulombAtom.packetDensity_mass 0 (hrpos n))
    (fun n x hx => by simpa only [sub_zero] using CoulombAtom.packetDensity_support 0 (hrpos n) hx)
    (fun n => CoulombAtom.packetDensity_radial (r n)) hg hcg

end CoulombAnalysis

end

end OAI
