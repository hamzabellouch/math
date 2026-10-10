import OAI.Probability.InvariantIsing.Gaussian.MPDensityProbability

namespace OAI

/-! Support of the literal MP density, with its zero atom distinguished. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal Topology
namespace InvariantIsing

lemma mp_edges_strict {α : ℝ} (hα : 0 < α) : marchenkoPasturA α < marchenkoPasturB α := by
  obtain ⟨ha,hb⟩ := mp_edge_centre_radius hα.le
  rw [ha,hb]
  linarith [sqrt_pos.mpr hα]

lemma mpDensity_pos {α x : ℝ} (hx : x ∈ Ioo (marchenkoPasturA α) (marchenkoPasturB α)) :
    0 < mpDensity α x := by
  have hx0 : 0 < x := (sq_nonneg (1-sqrt α)).trans_lt hx.1
  exact div_pos (sqrt_pos.mpr (mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr hx.1))) (by positivity)

lemma mp_interior_absolutelyContinuous {α : ℝ} :
    volume.restrict (Ioo (marchenkoPasturA α) (marchenkoPasturB α)) ≪ marchenkoPasturMeasure α := by
  let s := Ioo (marchenkoPasturA α) (marchenkoPasturB α)
  let f := fun x => ENNReal.ofReal (mpDensity α x)
  have hp : ∀ᵐ x ∂volume.restrict s, f x ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (ENNReal.ofReal_pos.mpr (mpDensity_pos hx)).ne'
  have ha := withDensity_absolutelyContinuous' (μ := volume.restrict s)
    (measurable_mpDensity α).ennreal_ofReal.aemeasurable hp
  apply ha.trans
  apply Measure.absolutelyContinuous_of_le
  rw [marchenkoPasturMeasure_eq_density,← withDensity_indicator measurableSet_Ioo,
    ← withDensity_indicator measurableSet_Icc]
  apply le_trans (withDensity_mono (ae_of_all _ fun x => ?_)) (Measure.le_add_left le_rfl)
  exact indicator_le_indicator_of_subset Ioo_subset_Icc_self (fun _ => bot_le) x

theorem mp_interval_subset_support {α : ℝ} (hα : 0 < α) :
    Icc (marchenkoPasturA α) (marchenkoPasturB α) ⊆ (marchenkoPasturMeasure α).support := by
  have hi : Ioo (marchenkoPasturA α) (marchenkoPasturB α) ⊆
      (marchenkoPasturMeasure α).support := by
    intro x hx
    apply mp_interior_absolutelyContinuous.support_mono
    apply Measure.interior_inter_support
    exact ⟨by simpa only [isOpen_Ioo.interior_eq] using hx,by rw [Measure.support_eq_univ]; trivial⟩
  rw [← closure_Ioo (mp_edges_strict hα).ne]
  exact closure_minimal hi Measure.isClosed_support

end InvariantIsing

end

end OAI
