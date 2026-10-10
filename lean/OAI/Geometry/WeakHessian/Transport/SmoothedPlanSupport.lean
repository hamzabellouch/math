import Mathlib
import OAI.Geometry.WeakHessian.Entropy.SmoothDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [SigmaFinite m] in
lemma density_zero_of_ae_law {u : Lp ℝ 2 m} (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {P : X → Prop} (hP : ∀ᵐ x ∂densityMeasure m u,P x) :
    ∀ᵐ x ∂m,¬P x → u x = 0 := by
  have H := (ae_withDensity_iff (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal)).mp hP
  filter_upwards [H,hun] with x hx hn hnp
  have he : ENNReal.ofReal (u x) = 0 := by
    by_contra hz
    exact hnp (hx hz)
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp he) hn

lemma timeAverageLaw_ae_of_tracks {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {P : X → Prop}
    (hPm : MeasurableSet {x | P x}) (hP : ∀ᵐ γ ∂π,∀ t : Time,P (γ t)) (s : ℝ) :
    ∀ᵐ x ∂timeAverageLaw π ν s,P x := by
  apply (ae_map_iff (continuous_timeAverageEval s).measurable.aemeasurable hPm).mpr
  have H : ∀ᵐ z : ℝ×Curve X ∂ν.prod π,∀ t : Time,P (z.2 t) := by
    exact ae_of_ae_map (μ := ν.prod π) (p := fun γ => ∀ t : Time,P (γ t))
      measurable_snd.aemeasurable (by simpa only [Measure.map_snd_prod,measure_univ,one_smul] using hP)
  filter_upwards [H] with z hz
  exact hz (clampTime (s-z.1))

lemma BoundedTracks.timeAverageLaw_bounded {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hb : BoundedTracks π) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ o : X,∃ R : ℝ,0 < R ∧ ∀ s : ℝ,∀ᵐ x ∂timeAverageLaw π ν s,dist x o ≤ R := by
  obtain ⟨o,R,hR,hb⟩ := hb
  exact ⟨o,R,hR,fun s => timeAverageLaw_ae_of_tracks ν (measurableSet_le (by fun_prop) measurable_const) hb s⟩

lemma timeAverageLaw_integrable_dist {π : Measure (Curve X)} [IsProbabilityMeasure π]
    (hb : BoundedTracks π) (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) (o : X) :
    Integrable (fun x => dist x o) (timeAverageLaw π ν s) := by
  let := isProbabilityMeasure_timeAverageLaw π ν s
  obtain ⟨a,R,hR,hb⟩ := hb.timeAverageLaw_bounded ν
  apply Integrable.of_bound (by fun_prop) (R+dist a o)
  filter_upwards [hb s] with x hx
  rw [Real.norm_of_nonneg dist_nonneg]
  exact (dist_triangle x a o).trans (by linarith)

lemma smoothDensity_integrable_dist
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hc : Continuous κ) (hi : Integrable κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1) (s : ℝ) (o : X) :
    Integrable (fun x => smoothDensity κ u s x*dist x o) m := by
  let : IsProbabilityMeasure π := hπ.1
  let := kernelMeasure_probability hi hn hm
  obtain ⟨hsn,_,_,_,hsl,_⟩ := hπ.smoothDensity_properties hB hu hun hlaw hnorm hc hi hn hm s
  have H := timeAverageLaw_integrable_dist hb (kernelMeasure κ) s o
  rw [← hsl] at H
  rw [densityMeasure,integrable_withDensity_iff_integrable_smul'
    (Lp.stronglyMeasurable _ |>.measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at H
  exact H.congr (by
    filter_upwards [hsn] with x hx
    simp only [ENNReal.toReal_ofReal hx,smul_eq_mul])

end WeakHessian

end
end

end OAI
