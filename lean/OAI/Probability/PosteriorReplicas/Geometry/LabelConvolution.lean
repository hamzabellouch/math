import OAI.Probability.PosteriorReplicas.Geometry.LabelEllipsoids

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma liftLabel_neg {d k : ℕ} (A : Rows d k) (y : Labels k) :
    liftLabel A (-y) = -liftLabel A y := by
  simp [liftLabel, Matrix.mulVec_neg, Finset.sum_neg_distrib]

lemma norm_liftLabel_sub_comm {d k : ℕ} (A : Rows d k) (x y : Labels k) :
    ‖liftLabel A (x-y)‖ = ‖liftLabel A (y-x)‖ := by
  rw [← neg_sub y x, liftLabel_neg, norm_neg]

def ellipsoidMass {d k : ℕ} (ν : Measure (Vec d)) (A : Rows d k) (y : Labels k) (r : ℝ) : ℝ≥0∞ :=
  ν {x | ‖liftLabel A (labels A x-y)‖ ≤ r}

@[fun_prop] lemma measurable_ellipsoidMass {d k : ℕ} (ν : Measure (Vec d)) [SFinite ν] (r : ℝ) :
    Measurable (fun z : Data d k => ellipsoidMass ν z.1 z.2 r) := by
  change Measurable (fun z : Data d k => ν ((Prod.mk z) ⁻¹'
    {q : Data d k × Vec d | ‖liftLabel q.1.1 (labels q.1.1 q.2-q.1.2)‖ ≤ r}))
  apply measurable_measure_prodMk_left
  exact measurableSet_le (by unfold labels; fun_prop) measurable_const

lemma lintegral_ellipsoidMass {d k : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {A : Rows d k} (hA : LinearIndependent ℝ A) (r : ℝ) :
    (∫⁻ y, ellipsoidMass ν A y r ∂volume) =
      ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ r} := by
  let S : Set (Labels k × Vec d) := {z | ‖liftLabel A (labels A z.2-z.1)‖ ≤ r}
  have hS : MeasurableSet S := measurableSet_le (by unfold labels; fun_prop) measurable_const
  have hs := (Measure.prod_apply (μ := volume) (ν := ν) hS).symm.trans
    (Measure.prod_apply_symm (μ := volume) (ν := ν) hS)
  change (∫⁻ y, ν ((Prod.mk y) ⁻¹' S) ∂volume) = _
  rw [hs]
  calc
    _ = ∫⁻ _x : Vec d, ENNReal.ofReal (gramVolume A) *
        volume {y : Labels k | labelNorm y ≤ r} ∂ν := by
      apply lintegral_congr
      intro x
      change volume {y : Labels k | ‖liftLabel A (labels A x-y)‖ ≤ r} = _
      simp_rw [norm_liftLabel_sub_comm A (labels A x)]
      exact label_ellipsoid_translate_volume hA (labels A x) r
    _ = _ := by simp

lemma normalized_density_integral_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    {a h : Y → ℝ≥0∞} (ha : Measurable a) (hh : Measurable h)
    (hat : ∀ y, a y ≠ ∞) :
    (∫⁻ y, (a y)⁻¹*h y ∂μ.withDensity a) ≤ ∫⁻ y, h y ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul _ ha (show Measurable (fun y => (a y)⁻¹*h y) from ha.inv.mul hh)]
  apply lintegral_mono
  intro y
  simp only [Pi.mul_apply]
  rw [← mul_assoc]
  by_cases haz : a y = 0
  · simp [haz]
  · rw [ENNReal.mul_inv_cancel haz (hat y), one_mul]

lemma normalized_inverse_density_integral {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    {a : Y → ℝ≥0∞} (ha : Measurable a) (hat : ∀ y, a y ≠ ∞) :
    (∫⁻ y, (a y)⁻¹ ∂μ.withDensity a) = μ {y | a y ≠ 0} := by
  rw [lintegral_withDensity_eq_lintegral_mul _ ha (show Measurable (fun y => (a y)⁻¹) from ha.inv)]
  rw [← lintegral_indicator_one (show MeasurableSet {y | a y ≠ 0} from
    (measurableSet_eq_fun ha measurable_const).compl)]
  apply lintegral_congr
  intro y
  by_cases haz : a y = 0
  · simp [haz]
  · simp [haz,ENNReal.mul_inv_cancel haz (hat y)]

lemma normalized_ellipsoidMass_integral_le {d k : ℕ} {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    {A : Rows d k} (hA : LinearIndependent ℝ A) (r : ℝ) :
    (∫⁻ y, (projectedDensity .spherical f A y)⁻¹ *
      ellipsoidMass ((sphereLaw d).withDensity f) A y r
      ∂volume.withDensity (projectedDensity .spherical f A)) ≤
      ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ r} := by
  rw [← lintegral_ellipsoidMass ((sphereLaw d).withDensity f) hA r]
  apply normalized_density_integral_le _ (by fun_prop) (by fun_prop)
  exact projectedDensity_ne_top .spherical hLt hfL A

end PosteriorReplicas
end

end OAI
