import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierDilationBarrier

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombAnalysis
open CoulombAtom

lemma cutoff_coulomb_majorant {ρ : TFSpace → ℝ} {x : TFSpace} {b M : ℝ}
    (hb : 0 < b) (hn : ∀ z, 0 ≤ ρ z) (hM : ∀ z, ρ z ≤ M) (z : TFSpace) :
    ρ z/‖x-z‖ ≤ M*truncatedCoulomb b (x-z)+ρ z/max b ‖x-z‖ := by
  by_cases hz : ‖x-z‖ < b
  · rw [max_eq_left hz.le,truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hz)]
    have hh := mul_le_mul_of_nonneg_right (hM z) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [mul_nonneg (hn z) (inv_pos.mpr hb).le]
  · rw [max_eq_right (le_of_not_gt hz),truncatedCoulomb,
      indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hz),mul_zero,zero_add]

lemma cutoff_coulomb_integrable {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z) {b : ℝ} (hb : 0 < b) (x : TFSpace) :
    Integrable (fun z => ρ z/max b ‖x-z‖) := by
  apply (hi.div_const b).mono'
    (hm.div (measurable_const.max (measurable_const.sub measurable_id).norm)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    change ‖ρ z/max b ‖x-z‖‖ ≤ ρ z/b
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (hb.le.trans (le_max_left _ _)))]
    exact div_le_div_of_nonneg_left (hn z) hb (le_max_left _ _))

lemma potential_cutoff_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z) {M b : ℝ} (hM : ∀ z, ρ z ≤ M)
    (hb : 0 < b) (x : TFSpace) :
    tfPotential ρ x ≤ 2*Real.pi*M*b^2+∫ z, ρ z/max b ‖x-z‖ := by
  have hk : Integrable (fun z => truncatedCoulomb b (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable b).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable b)
  calc
    _ ≤ ∫ z, M*truncatedCoulomb b (x-z)+ρ z/max b ‖x-z‖ := integral_mono
      (local_bounded_potential_integrable hm hi hb hn (fun z _ => hM z))
      ((hk.const_mul M).add (cutoff_coulomb_integrable hm hi hn hb x))
      (cutoff_coulomb_majorant hb hn hM)
    _ = _ := by
      rw [integral_add (hk.const_mul M) (cutoff_coulomb_integrable hm hi hn hb x),
        integral_const_mul,integral_sub_left_eq_self,truncatedCoulomb,integral_indicator measurableSet_ball]
      simp only [one_div]
      rw [integral_coulomb_ball hb]
      ring

lemma cutoff_potential_decay {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    {v : ι → TFSpace} (hv : Tendsto (fun i => ‖v i‖) F atTop)
    {ρ : TFSpace → ℝ} (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun i => ∫ z, ρ z/max b ‖v i-z‖) F (𝓝 0) := by
  have hh := tendsto_integral_filter_of_dominated_convergence (l := F)
    (F := fun i z => ρ z/max b ‖v i-z‖) (fun z => ρ z/b)
    (f := fun _ : TFSpace => (0:ℝ))
    (Eventually.of_forall (fun i => (cutoff_coulomb_integrable hm hi hn hb (v i)).aestronglyMeasurable))
    (Eventually.of_forall (fun i => ae_of_all _ (fun z => by
      rw [Real.norm_of_nonneg (div_nonneg (hn z) (hb.le.trans (le_max_left _ _)))]
      exact div_le_div_of_nonneg_left (hn z) hb (le_max_left _ _))))
    (hi.div_const b) (ae_of_all _ (fun z => ?_))
  · simpa only [integral_zero] using hh
  · apply Tendsto.const_div_atTop
    apply tendsto_atTop_mono (fun i => le_max_right b ‖v i-z‖)
    apply tendsto_atTop_mono (fun i => ?_) (show Tendsto (fun i => ‖v i‖-‖z‖) F atTop from by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right F (-‖z‖) hv)
    linarith [norm_le_norm_sub_add (v i) z]

theorem bounded_L1_potential_decay {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    {v : ι → TFSpace} (hv : Tendsto (fun i => ‖v i‖) F atTop)
    {ρ : TFSpace → ℝ} (hm : Measurable ρ) (hi : Integrable ρ)
    (hn : ∀ z, 0 ≤ ρ z) {M : ℝ} (hM : 0 ≤ M) (hMb : ∀ z, ρ z ≤ M) :
    Tendsto (fun i => tfPotential ρ (v i)) F (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let b := Real.sqrt (ε/(8*Real.pi*(M+1)))
  have hd : 0 < 8*Real.pi*(M+1) := by positivity
  have hb : 0 < b := Real.sqrt_pos.mpr (div_pos hε hd)
  have hbs : b^2 = ε/(8*Real.pi*(M+1)) := Real.sq_sqrt (div_pos hε hd).le
  have hmul : b^2*(8*Real.pi*(M+1)) = ε := by rw [hbs]; exact div_mul_cancel₀ ε hd.ne'
  have hnear : 2*Real.pi*M*b^2 < ε/2 := by
    nlinarith [mul_pos Real.pi_pos (sq_pos_of_pos hb)]
  have hfar := cutoff_potential_decay hv hm hi hn hb
  filter_upwards [hfar.eventually (gt_mem_nhds (half_pos hε))] with i hi'
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (tfPotential_nonneg (ae_of_all _ hn) _)]
  exact lt_of_le_of_lt (potential_cutoff_le hm hi hn hMb hb (v i)) (by linarith)
end CoulombAnalysis

end

end OAI
