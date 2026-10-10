import OAI.MeasureTheory.Falconer.Geometry.EuclideanWeakApproximation
import OAI.MeasureTheory.Falconer.Geometry.SurfaceTestNorm
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! Continuity of the radial test norm from finite positive Riesz energy. -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem nullSingletonClass_of_finite_rieszEnergy {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] {s : ℝ} (hs : 0 < s) (hμ : PlanarFalconer.rieszEnergyOn μ s < ∞) :
    NullSingletonClass μ := by
  have hf := ae_lt_top (μ := μ.prod μ)
    (show Measurable (fun z : Space d × Space d => (edist z.1 z.2)^(-s)) by fun_prop) hμ.ne
  have hneq : ∀ᵐ z : Space d × Space d ∂μ.prod μ, z.1 ≠ z.2 := by
    filter_upwards [hf] with z hz he
    simp only [he, edist_self, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hs), lt_self_iff_false] at hz
  have hdiag : μ.prod μ {z : Space d × Space d | z.1 = z.2} = 0 := by
    simpa only [ae_iff, not_not] using hneq
  constructor
  intro x
  have hsub : ({x} : Set (Space d)) ×ˢ {x} ⊆ {z : Space d × Space d | z.1 = z.2} := by
    rintro ⟨y,z⟩ ⟨hy,hz⟩
    exact hy.trans hz.symm
  have h := measure_mono_null hsub hdiag
  rw [Measure.prod_prod] at h
  exact (mul_eq_zero.mp h).elim id id

theorem continuousAt_radialDirection_center {d : ℕ} (x y : Space d) (hy : y ≠ x) :
    ContinuousAt (fun z => radialDirection z y) x := by
  have hd : ContinuousAt (fun z : Space d => y-z) x :=
    (continuous_const.sub continuous_id).continuousAt
  exact (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))).smul hd

theorem continuous_atomless_radial_ambient_test {d : ℕ} (α : Measure (Space d))
    [IsFiniteMeasure α] [NullSingletonClass α] (F : BoundedContinuousFunction (Space d) ℝ) :
    Continuous (fun x => ∫ w, F w ∂α.map (radialDirection x)) := by
  have hm (x : Space d) : Measurable (radialDirection x) := by unfold radialDirection; fun_prop
  simp_rw [integral_map (hm _).aemeasurable F.continuous.aestronglyMeasurable]
  rw [continuous_iff_continuousAt]
  intro x
  apply continuousAt_of_dominated (bound := fun _ : Space d => ‖F‖)
  · exact Eventually.of_forall (fun z => (F.continuous.measurable.comp (hm z)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun _ => Eventually.of_forall (fun _ => F.norm_coe_le_norm _))
  · exact integrable_const _
  · filter_upwards [(show ∀ᵐ y ∂α, y ≠ x from by rw [ae_iff]; simp)] with y hy
    exact F.continuous.continuousAt.comp (continuousAt_radialDirection_center x y hy)

theorem surfaceTestNorm_atomless_radial_measurable {n : ℕ} (α : Measure (Space (n+1)))
    [IsFiniteMeasure α] [NullSingletonClass α] (q : ℝ) :
    Measurable (fun x => surfaceTestNorm q (α.map (radialDirection x))) := by
  apply LowerSemicontinuous.measurable
  unfold surfaceTestNorm
  apply lowerSemicontinuous_biSup
  intro F _
  exact (ENNReal.continuous_ofReal.comp (continuous_atomless_radial_ambient_test α F).norm).lowerSemicontinuous

end Falconer

end OAI
