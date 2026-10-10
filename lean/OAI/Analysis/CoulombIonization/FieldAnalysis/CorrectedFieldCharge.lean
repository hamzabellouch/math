import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SharpOrdinaryCapBarrier

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombAnalysis
open CoulombAtom

lemma finite_L1_tail_decay {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    {R : ι → ℝ} (hR : Tendsto R F atTop) {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hn : ∀ x, 0 ≤ ρ x) :
    Tendsto (fun i => ∫ x in {x : Space | R i < ‖x‖}, ρ x) F (𝓝 0) := by
  have hh := tendsto_integral_filter_of_dominated_convergence (l := F)
    (F := fun i => {x : Space | R i < ‖x‖}.indicator ρ) (f := fun _ : Space => (0:ℝ)) ρ
    (Eventually.of_forall (fun i => (hm.indicator (measurableSet_lt measurable_const measurable_norm)).aestronglyMeasurable))
    (Eventually.of_forall (fun i => ae_of_all _ (fun x => by
      by_cases hx : R i < ‖x‖
      · rw [indicator_of_mem (show x ∈ {x : Space | R i < ‖x‖} from hx), Real.norm_of_nonneg (hn x)]
      · rw [indicator_of_notMem (show x ∉ {x : Space | R i < ‖x‖} from hx),norm_zero]; exact hn x))) hi
    (ae_of_all _ (fun x => ?_))
  · simpa only [integral_indicator (measurableSet_lt measurable_const measurable_norm),integral_zero] using hh
  · apply tendsto_const_nhds.congr'
    filter_upwards [hR.eventually_ge_atTop ‖x‖] with i hi
    exact (indicator_of_notMem (show x ∉ {x : Space | R i < ‖x‖} from not_lt.mpr hi) ρ).symm

lemma potential_sphereMean_mass_le {e : Space → ℝ} (hm : Measurable e)
    (hi : Integrable e) (hn : ∀ x, 0 ≤ e x) {p : Space} (hp : p ≠ 0) :
    sphereMean (tfPotential e) p ≤ (∫ x, e x)/‖p‖ := by
  rw [L1_sphereMean_potential hm hi hn hp, ←integral_div]
  exact integral_mono (density_shell_integrable hm hi hn hp) (hi.div_const _) (fun z =>
    div_le_div_of_nonneg_left (hn z) (norm_pos_iff.mpr hp) (le_max_left _ _))

theorem corrected_field_charge {ρ e : Space → ℝ} {Z M r : ℝ}
    (hr : 0 < r) (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hem : Measurable e) (hei : Integrable e) (hen : ∀ x, 0 ≤ e x)
    (hfield : ∀ x, r ≤ ‖x‖ → 0 ≤ Z/‖x‖-tfPotential ρ x+tfPotential e x) :
    (∫ x, ρ x)-Z ≤ ∫ x, e x := by
  have hR : Tendsto (fun n : ℕ => (n:ℝ)+r+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_atTop_add_const_right atTop r tendsto_natCast_atTop_atTop)
  have hlim := (finite_L1_tail_decay hR hm hi hn).const_add (∫ x, e x)
  have hbound (R : ℝ) (hR : r ≤ R) :
      (∫ x, ρ x)-Z ≤ (∫ x, e x)+(∫ x in {x : Space | R < ‖x‖}, ρ x) := by
    have hRp : 0 < R := hr.trans_le hR
    obtain ⟨p,hpR⟩ := exists_norm_eq (E := Space) hRp.le
    have hp : p ≠ 0 := norm_pos_iff.mp (hpR ▸ hRp)
    have hf : Integrable (fun g : SpatialRotation => Z/‖rotate g p‖-tfPotential ρ (rotate g p)) rotationMeasure := by
      simp only [(rotate _).norm_map]
      exact (integrable_const _).sub (L1_potential_rotation_integrable hm hi hn hp)
    have hfe := hf.add (L1_potential_rotation_integrable hem hei hen hp)
    have hnon : 0 ≤ ∫ g : SpatialRotation, Z/‖rotate g p‖-tfPotential ρ (rotate g p)+tfPotential e (rotate g p) ∂rotationMeasure :=
      integral_nonneg (fun g : SpatialRotation =>
      hfield (rotate g p) (by simpa only [(rotate _).norm_map,hpR] using hR))
    rw [integral_add hf (L1_potential_rotation_integrable hem hei hen hp)] at hnon
    change 0 ≤ sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p+sphereMean (tfPotential e) p at hnon
    have hρ := (sphereMean_field_bracket hm hi hM hn hb Z hp).2
    have he := potential_sphereMean_mass_le hem hei hen hp
    rw [hpR] at hρ he
    have hh : ((∫ x, ρ x)-Z) / R ≤ ((∫ x, e x)+(∫ x in {x : Space | R < ‖x‖}, ρ x))/R := by
      rw [sub_div,add_div]
      rw [sub_div] at hρ
      linarith
    exact (div_le_div_iff_of_pos_right hRp).mp hh
  have hh := ge_of_tendsto hlim (Eventually.of_forall (fun n : ℕ => hbound ((n:ℝ)+r+1) (by linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n])))
  simpa only [add_zero] using hh
end CoulombAnalysis

end

end OAI
