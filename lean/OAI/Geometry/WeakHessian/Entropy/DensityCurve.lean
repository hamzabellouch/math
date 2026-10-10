import Mathlib
import OAI.Geometry.WeakHessian.Entropy.EntropyContact
import OAI.Geometry.WeakHessian.HeatFlow.HeatProbability
import OAI.Geometry.WeakHessian.Entropy.CompressedDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory TopologicalSpace WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

lemma norm_lowerSemicontinuous_of_inner_continuous
    {T H : Type*} [TopologicalSpace T] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u : T → H} (hu : ∀ f : H, Continuous (fun t => ⟪u t,f⟫_ℝ)) :
    LowerSemicontinuous (fun t => ‖u t‖) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : 0 ≤ r
  · have he : (fun t => ‖u t‖) ⁻¹' Iic r =
        ⋂ f : H, {t | ⟪u t,f⟫_ℝ ≤ r*‖f‖} := by
      ext t
      simp only [mem_preimage,mem_Iic,mem_iInter,mem_ofPred_eq]
      constructor
      · intro ht f
        exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
      · intro ht
        have h := ht (u t)
        rw [real_inner_self_eq_norm_sq,pow_two] at h
        by_cases hz : ‖u t‖ = 0
        · rwa [hz]
        · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp h
    rw [he]
    exact isClosed_iInter fun f => isClosed_le (hu f) continuous_const
  · have he : (fun t => ‖u t‖) ⁻¹' Iic r = ∅ := by
      ext t
      simp only [mem_preimage,mem_Iic,mem_empty_iff_false,iff_false]
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hr) (norm_nonneg _))
    rw [he]; exact isClosed_empty

lemma stronglyMeasurable_of_inner_continuous
    {T H : Type*} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
    {u : T → H} (hu : ∀ f : H, Continuous (fun t => ⟪u t,f⟫_ℝ)) :
    StronglyMeasurable u := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  have hb : IsTopologicalBasis {s : Set H | ∃ x r, s = Metric.ball x r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨x,r,rfl⟩; exact Metric.isOpen_ball
    · intro x s hx hs
      obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hs x hx
      exact ⟨Metric.ball x r,⟨x,r,rfl⟩,Metric.mem_ball_self hr,hsub⟩
  have hm : Measurable u := by
    change @Measurable T H _ (borel H) u
    rw [hb.borel_eq_generateFrom]
    apply measurable_generateFrom
    rintro s ⟨x,r,rfl⟩
    have hl : LowerSemicontinuous (fun t => ‖u t-x‖) :=
      norm_lowerSemicontinuous_of_inner_continuous fun f => by
        convert (hu f).sub (continuous_const (y := ⟪x,f⟫_ℝ)) using 1
        funext t
        simp only [inner_sub_left,Pi.sub_apply]
    convert hl.measurable (measurableSet_Iio (a := r)) using 1
    ext t
    simp [Metric.mem_ball,dist_eq_norm]
  exact hm.stronglyMeasurable

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma IsTestPlan.continuous_density_inner (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {u : Time → Lp ℝ 2 m} (hu : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t)) (f : Lp ℝ 2 m) :
    Continuous (fun t => ⟪u t,f⟫_ℝ) := by
  have he (t : Time) : ⟪u t,f⟫_ℝ = ∫ γ, f (γ t) ∂π := by
    rw [real_inner_comm,← integral_densityMeasure_L2 _ _ (hu t),hlaw t]
    apply integral_map (continuous_eval_const t).measurable.aemeasurable
    obtain ⟨B,hB⟩ := hπ.2.1
    exact (Lp.memLp f).aestronglyMeasurable.mono_ac (Measure.absolutelyContinuous_of_le_smul (hB t))
  simp_rw [he]
  apply hπ.continuous_integral_eval_local hfin hb
  intro o R hR
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin _ Metric.isBounded_ball⟩
  exact ((Lp.memLp f).mono_measure Measure.restrict_le_self).integrable (by norm_num)

lemma IsTestPlan.exists_L2_density_curve (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∃ B : ℝ≥0, ∃ u : Time → Lp ℝ 2 m,
      StronglyMeasurable u ∧
      (∀ t, ∀ᵐ x ∂m, 0 ≤ u t x) ∧ (∀ t, ∀ᵐ x ∂m, |u t x| ≤ B) ∧
      (∀ t, Integrable (u t) m) ∧ (∀ t, ∫ x, u t x ∂m = 1) ∧
      (∀ t, densityMeasure m (u t) = π.map (fun γ => γ t)) ∧
      (∀ t, ‖u t‖^2 ≤ (B : ℝ)) ∧ (∀ f, Continuous (fun t => ⟪u t,f⟫_ℝ)) := by
  classical
  let : IsProbabilityMeasure π := hπ.1
  obtain ⟨B,hB⟩ := hπ.2.1
  have hex (t : Time) := exists_compressedDensity (hB t)
  choose u hun hub hui hum hul hunorm using hex
  have hm (t : Time) : ∫ x, u t x ∂m = 1 := by
    simpa [Measure.real,Measure.map_apply (continuous_eval_const t).measurable MeasurableSet.univ] using hum t
  have hnorm (t : Time) : ‖u t‖^2 ≤ (B : ℝ) := by
    simpa [Measure.real,Measure.map_apply (continuous_eval_const t).measurable MeasurableSet.univ] using hunorm t
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hc := hπ.continuous_density_inner hfin hb hun hul
  exact ⟨B,u,stronglyMeasurable_of_inner_continuous hc,hun,hub,hui,hm,hul,hnorm,hc⟩

end WeakHessian

end
end

end OAI
