import Mathlib
import OAI.Geometry.WeakHessian.Measure.InlinedFile0

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile86
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m ν : Measure X}

lemma IsTestPlan.of_local_measure_le_smul {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • ν) :
    IsTestPlan ν π := by
  obtain ⟨o,R,hR,htracks⟩ := hb
  obtain ⟨C,hC⟩ := hm o (R+1) (by linarith)
  obtain ⟨D,hD⟩ := hπ.2.1
  refine ⟨hπ.1,⟨D*C,fun t => ?_⟩,hπ.2.2⟩
  have ha : ∀ᵐ x ∂Measure.map (fun γ : Curve X => γ t) π,x ∈ Metric.ball o (R+1) := by
    apply (ae_map_iff (continuous_eval_const t).measurable.aemeasurable Metric.isOpen_ball.measurableSet).mpr
    filter_upwards [htracks] with γ hγ
    exact lt_of_le_of_lt (hγ t) (by linarith)
  calc
    Measure.map (fun γ : Curve X => γ t) π = (Measure.map (fun γ : Curve X => γ t) π).restrict (Metric.ball o (R+1)) :=
      (Measure.restrict_eq_self_of_ae_mem ha).symm
    _ ≤ ((D:ℝ≥0∞) • m).restrict (Metric.ball o (R+1)) := Measure.restrict_mono_measure (hD t) _
    _ = (D:ℝ≥0∞) • m.restrict (Metric.ball o (R+1)) := Measure.restrict_smul _ _ _
    _ ≤ (D:ℝ≥0∞) • ((C:ℝ≥0∞) • ν) := by gcongr
    _ = ((D*C:ℝ≥0):ℝ≥0∞) • ν := by rw [smul_smul,ENNReal.coe_mul]

lemma LocallyL2.of_local_measure_le_smul {f : X → ℝ} (hf : LocallyL2 m f)
    (hm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,ν.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m) :
    LocallyL2 ν f := by
  intro o R hR
  obtain ⟨C,hC⟩ := hm o R hR
  apply MemLp.of_measure_le_smul (c := (C:ℝ≥0∞)) (by simp) _ (hf o R hR)
  simpa only [Measure.restrict_smul,Measure.restrict_restrict Metric.isOpen_ball.measurableSet,inter_self] using
    Measure.restrict_mono_measure hC (Metric.ball o R)

lemma IsLocalWeakUpperGradient.of_local_measure_le_smul {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hν : ν ≪ m)
    (hm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,ν.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m) :
    IsLocalWeakUpperGradient ν f D := by
  refine ⟨hD.1.of_local_measure_le_smul hm,hν.ae_le hD.2.1,?_⟩
  intro π hπ hb
  exact hD.2.2 π (hπ.of_local_measure_le_smul hb hm) hb

lemma IsMinimalLocalWeakUpperGradient.change_measure_local {f D : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) (hν : ν ≪ m) (hm : m ≪ ν)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,ν.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • ν) :
    IsMinimalLocalWeakUpperGradient ν f D := by
  refine ⟨hD.1.of_local_measure_le_smul hν hνm,?_⟩
  intro E hE
  exact hν.ae_le (hD.2 E (hE.of_local_measure_le_smul hm hmν))

lemma weakGradient_eq_of_locally_comparable (hν : ν ≪ m) (hm : m ≪ ν)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,ν.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • ν)
    (f : X → ℝ) : weakGradient m f =ᵐ[m] weakGradient ν f := by
  by_cases hf : ∃ D,IsMinimalLocalWeakUpperGradient m f D
  · have hfν : ∃ D,IsMinimalLocalWeakUpperGradient ν f D :=
      ⟨hf.choose,hf.choose_spec.change_measure_local hν hm hνm hmν⟩
    have hDm := weakGradient_isMinimal hf
    have hDν := (weakGradient_isMinimal hfν).change_measure_local hm hν hmν hνm
    filter_upwards [hDm.2 _ hDν.1,hDν.2 _ hDm.1] with x hx hy
    exact le_antisymm hx hy
  · have hfν : ¬∃ D,IsMinimalLocalWeakUpperGradient ν f D := by
      rintro ⟨D,hD⟩
      exact hf ⟨D,hD.change_measure_local hm hν hmν hνm⟩
    simp only [weakGradient,dite_eq_right hf,dite_eq_right hfν]
    exact Filter.EventuallyEq.rfl
end WeakHessian

end
end InlinedFile86

end OAI
