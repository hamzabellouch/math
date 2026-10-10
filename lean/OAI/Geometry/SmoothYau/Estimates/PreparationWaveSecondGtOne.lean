import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.GlobalPrepDualNorm

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ENNReal NNReal Topology
namespace YauCounterexamples
variable {X G : Type*} [MeasurableSpace X] [MeasurableSpace G]
  [AddGroup G] [MeasurableAdd₂ G]
  (μ : Measure X) [SFinite μ] (ν : Measure G) [SFinite ν]
  [ν.IsAddLeftInvariant]

theorem periodic_phase_average (a : X → G) (ha : Measurable a)
    {E : Set G} (hE : MeasurableSet E) :
    (∫⁻ τ, μ {x | a x + τ ∈ E} ∂ν) = μ univ * ν E := by
  have hh : Measurable (fun p : X × G => E.indicator (fun _ => (1 : ℝ≥0∞)) (a p.1+p.2)) :=
    (measurable_const.indicator hE).comp ((ha.comp measurable_fst).add measurable_snd)
  have hleft (τ : G) : (∫⁻ x, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂μ) =
      μ {x | a x+τ ∈ E} := by
    rw [show (fun x => E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ)) =
      ((fun x => a x+τ) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) by
        funext x; rfl]
    rw [lintegral_indicator (hE.preimage (ha.add_const τ)), lintegral_one, Measure.restrict_apply_univ]
    rfl
  have hright (x : X) : (∫⁻ τ, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂ν) = ν E := by
    rw [show (fun τ => E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ)) =
      ((fun τ => a x+τ) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) by
        funext τ; rfl]
    have hm : Measurable (fun τ : G => a x + τ) := measurable_const.add measurable_id
    rw [lintegral_indicator (hE.preimage hm), lintegral_one, Measure.restrict_apply_univ]
    exact measure_preimage_add ν (a x) E
  calc
    _ = ∫⁻ τ, ∫⁻ x, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂μ ∂ν := by simp_rw [hleft]
    _ = ∫⁻ x, ∫⁻ τ, E.indicator (fun _ => (1 : ℝ≥0∞)) (a x+τ) ∂ν ∂μ :=
      (lintegral_lintegral_swap hh.aemeasurable).symm
    _ = _ := by simp [hright,mul_comm]

theorem exists_periodic_phase_mass [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (a : X → G) (ha : Measurable a) {E : Set G} (hE : MeasurableSet E) :
    ∃ τ : G, μ univ * ν E ≤ μ {x | a x+τ ∈ E} := by
  have hi := periodic_phase_average μ ν a ha hE
  obtain ⟨τ,hτ⟩ := exists_lintegral_le (μ:=ν)
    (f:=fun τ => μ {x | a x+τ ∈ E}) (by rw [hi]; exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  exact ⟨τ,hi ▸ hτ⟩
end YauCounterexamples

end


namespace YauCounterexamples
noncomputable section
open Set Function MeasureTheory Metric
open scoped ENNReal

lemma preparationWaveSecond_gt_one_of_abs {t : ℝ} (ht : |t| < 1/6) :
    1 < preparationWaveSecond t := by
  have hπ := Real.pi_pos
  have harg : |2*Real.pi*t| < Real.pi/3 := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    nlinarith
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (2*Real.pi*t))
    (by linarith : Real.pi/3 ≤ Real.pi) harg
  rw [Real.cos_pi_div_three,Real.cos_abs] at hcos
  dsimp [preparationWaveSecond]
  linarith

lemma preparationWaveSecond_gt_one_of_circle {t : ℝ}
    (ht : (t : UnitAddCircle) ∈ ball 0 (1/6)) : 1 < preparationWaveSecond t := by
  have habs : |t-(round t : ℝ)| < 1/6 := by
    simpa only [mem_ball,dist_zero_right,AddCircle.norm_eq,inv_one,one_mul,mul_one] using ht
  have he := preparationWaveSecond_periodic.sub_int_mul_eq (x:=t) (round t)
  rw [mul_one] at he
  rw [←he]
  exact preparationWaveSecond_gt_one_of_abs habs

lemma preparation_phase_fraction :
    (volume : Measure UnitAddCircle) (ball 0 (1/6)) = (1/3 : ℝ≥0∞) := by
  rw [←measure_congr (AddCircle.closedBall_ae_eq_ball (x:=(0:UnitAddCircle)) (ε:=1/6)),
    AddCircle.volume_closedBall]
  norm_num [ENNReal.ofReal_div_of_pos]

theorem exists_preparation_phase {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : X → ℝ) (hs : Measurable s) (N : ℝ) :
    ∃ τ : ℝ, μ univ*(1/3 : ℝ≥0∞) ≤ μ {x | 1 < preparationWaveSecond (N*s x+τ)} := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  have ha : Measurable (fun x => ((N*s x : ℝ) : UnitAddCircle)) :=
    (AddCircle.continuous_mk' (1:ℝ)).measurable.comp (measurable_const.mul hs)
  obtain ⟨τ,hτ⟩ := exists_periodic_phase_mass μ (volume : Measure UnitAddCircle)
    (fun x => ((N*s x : ℝ) : UnitAddCircle)) ha (E:=ball 0 (1/6)) measurableSet_ball
  obtain ⟨τ,rfl⟩ := Quotient.exists_rep τ
  refine ⟨τ,?_⟩
  rw [preparation_phase_fraction] at hτ
  refine hτ.trans (measure_mono ?_)
  intro x hx
  apply preparationWaveSecond_gt_one_of_circle
  exact hx
end
end YauCounterexamples

end OAI
